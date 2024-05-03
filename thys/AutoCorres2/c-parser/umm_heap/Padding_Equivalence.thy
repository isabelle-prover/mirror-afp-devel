(*
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory Padding_Equivalence
  imports
    TypHeap
    SepCode
    CProof
    More_Lib
begin

lemma field_lookup_padding_field_name:
  fixes
  t:: "('a, 'b) typ_info " and
  st :: "('a, 'b) typ_info_struct" and
  ts :: "('a, 'b) typ_info_tuple list" and
  x :: "('a, 'b) typ_info_tuple"
shows
"field_lookup t [f] n = Some (s, m) \<Longrightarrow> padding_field_name f \<Longrightarrow> wf_padding t \<Longrightarrow>
   is_padding_tag s"
"field_lookup_struct st [f] n = Some (s, m) \<Longrightarrow> padding_field_name f \<Longrightarrow> wf_padding_struct st \<Longrightarrow>
   is_padding_tag s"
"field_lookup_list ts [f] n = Some (s, m) \<Longrightarrow> padding_field_name f \<Longrightarrow> wf_padding_list ts \<Longrightarrow>
   is_padding_tag s"
"field_lookup_tuple x [f] n = Some (s, m) \<Longrightarrow> padding_field_name f \<Longrightarrow> wf_padding_tuple x \<Longrightarrow>
   is_padding_tag s"
  by (induct t and st and ts and x arbitrary: n m and n m and n m and n m)
    (auto split: if_split_asm option.splits)

lemma field_lookup_access_ti_take_drop':
  fixes t::"('a, 'b) typ_info"
  and st::"('a, 'b) typ_info_struct"
  and ts::"('a, 'b) typ_info_tuple list"
  and x::"('a, 'b) typ_info_tuple"
shows
  "field_lookup t f m = Some (s, m + n) \<Longrightarrow> wf_fd t \<Longrightarrow> wf_desc t \<Longrightarrow> wf_size_desc t \<Longrightarrow> length bs = size_td t \<Longrightarrow>
     access_ti s v (take (size_td s) (drop n bs)) =
       (take (size_td s) (drop n (access_ti t v bs)))"

  "field_lookup_struct st f m = Some (s, m + n) \<Longrightarrow> wf_fd_struct st \<Longrightarrow> wf_desc_struct st \<Longrightarrow> wf_size_desc_struct st \<Longrightarrow> length bs = size_td_struct st  \<Longrightarrow>
     access_ti s v (take (size_td s) (drop n bs)) =
       (take (size_td s) (drop n (access_ti_struct st v bs)))"

  "field_lookup_list ts f m = Some (s, m + n) \<Longrightarrow> wf_fd_list ts \<Longrightarrow> wf_desc_list ts \<Longrightarrow> wf_size_desc_list ts \<Longrightarrow> length bs = size_td_list ts \<Longrightarrow>
     access_ti s v (take (size_td s) (drop n bs)) =
       (take (size_td s) (drop n (access_ti_list ts v bs)))"

  "field_lookup_tuple x f m = Some (s, m + n) \<Longrightarrow> wf_fd_tuple x \<Longrightarrow> wf_desc_tuple x \<Longrightarrow> wf_size_desc_tuple x \<Longrightarrow> length bs = size_td_tuple x \<Longrightarrow>
     access_ti s v (take (size_td s) (drop n bs)) =
       (take (size_td s) (drop n (access_ti_tuple x v bs)))"
proof (induct t and st and ts and x arbitrary: f m n s bs v and f m n s bs v and f m n s bs v and f m n s bs v)
  case (TypDesc algn st nm)
  then show ?case 
    by (auto split: if_split_asm)
       (metis TypDesc.prems(2) TypDesc.prems(5) access_ti.simps le_refl length_fa_ti take_all)
next
  term TypDesc
  case (TypScalar algn st d)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto
  from Cons_typ_desc.prems obtain
    lbs: "length bs = size_td_tuple x + size_td_list fs" and
    wf_fd_x: "wf_fd_tuple (DTuple d nm y)" and
    wf_desc_x: "wf_desc_tuple (DTuple d nm y)" and
    wf_fd_fs: "wf_fd_list fs" and
    wf_size_desc_x: "wf_size_desc_tuple (DTuple d nm y)" and
    wf_size_desc_fs: "wf_size_desc_list fs" and
    nm_notin:  "nm \<notin> dt_snd ` set fs" and
    wf_desc_fs: "wf_desc_list fs" and
    commutes: "fu_commutes (update_ti_t d) (update_ti_list_t fs)"
    by (auto simp add: x)

  from lbs
  have lbs_drop: "length (drop (size_td_tuple x) bs) = size_td_list fs"
    by simp

  from lbs
  have lbs_take: "length (take (size_td_tuple x) bs) = size_td_tuple (DTuple d nm y)"
    by (simp add: x)

  from lbs wf_fd_x
  have eq1: "length (access_ti d v (take (size_td d) bs)) = size_td d"
    by (metis lbs_take length_fa_ti size_td_tuple.simps wf_fd_tuple.simps x)

  from Cons_typ_desc.prems obtain f1 fxs
    where f: "f = f1#fxs"
    by (cases f) auto

  show ?case
  proof (cases "f1 = nm")
    case True
    show ?thesis
    proof (cases "field_lookup d fxs m")
      case None
      from Cons_typ_desc.prems field_lookup_list_None [OF nm_notin]
      have False
        by (simp add: True None f x)
      thus ?thesis by simp
    next
      case (Some r)
      from Cons_typ_desc.prems have r: "r = (s, m + n)"
        by (simp add: x True Some f)
      hence fl: "field_lookup_tuple (DTuple d nm y) f m = Some (s, m + n)"
        by  (simp add: f True Some r)

      from td_set_wf_size_desc(4)[OF wf_size_desc_x td_set_tuple_field_lookup_tupleD, OF fl]
      have "wf_size_desc s" .
      from wf_size_desc_gt(1)[OF this]
      have "0 < size_td s" .


      with td_set_tuple_offset_size_m [OF td_set_tuple_field_lookup_tupleD, OF fl]
      have n_le: "n < size_td d"
        by auto

      have bound: "size_td s + (m + n - m) \<le> size_td_tuple (DTuple d nm y)" by fact
      from bound
      have take_eq: "(take (size_td s) (drop n (take (size_td d) bs))) =
         (take (size_td s) (drop n bs))"
        by (simp add: take_drop)

      from Cons_typ_desc.hyps(1)[simplified x, OF fl wf_fd_x wf_desc_x wf_size_desc_x lbs_take, of v] lbs bound
      show ?thesis by (simp add: x True Some r take_eq eq1)
    qed
  next
    case False
    with Cons_typ_desc.prems
    have fl: "field_lookup_list fs (f1 # fxs) (m + size_td d) = Some (s, m + n)"
      by (clarsimp simp add: x f False)
    hence n_bound: "size_td d \<le> n"
      by (meson field_lookup_offset_le(3) nat_add_left_cancel_le)

    from fl
    have fl: "field_lookup_list fs (f1 # fxs) (m + size_td d) = Some (s, (m + size_td d) + (n - size_td d))"
      by (metis Nat.diff_cancel field_lookup_list_offset2 field_lookup_list_offsetD)
    from n_bound
    have take_eq: "(take (size_td s) (drop (n - size_td d + size_td d) bs)) =
            (take (size_td s) (drop n bs))"
      by simp


    from Cons_typ_desc.hyps(2) [OF fl wf_fd_fs wf_desc_fs wf_size_desc_fs lbs_drop, of v]
      False n_bound
    show ?thesis
      by (simp add: x f eq1)
  qed
next
  case (DTuple_typ_desc d nm y)
  then show ?case apply (cases f) by (auto split: if_split_asm)
qed

lemma field_lookup_access_ti_take_drop:
  "field_lookup t f 0 = Some (s, n) \<Longrightarrow> wf_fd t \<Longrightarrow> wf_desc t \<Longrightarrow> wf_size_desc t \<Longrightarrow> length bs = size_td t \<Longrightarrow>
     access_ti s v (take (size_td s) (drop n bs)) =
       (take (size_td s) (drop n (access_ti t v bs)))"
  using field_lookup_access_ti_take_drop' [where m=0] by auto

lemma field_lookup_nth_focus':
  fixes t::"('a, 'b) typ_info"
  and st::"('a, 'b) typ_info_struct"
  and ts::"('a, 'b) typ_info_tuple list"
  and x::"('a, 'b) typ_info_tuple"
shows
"\<lbrakk>field_lookup t f m = Some (s, m + n); n \<le> i; i < n + size_td s; length bs = size_td t;
  wf_fd t; wf_desc t; wf_size_desc t\<rbrakk> \<Longrightarrow>
   access_ti t v bs ! i = access_ti s v (take (size_td s) (drop n bs)) ! (i - n)"

"\<lbrakk>field_lookup_struct st f m = Some (s, m + n); n \<le> i; i < n + size_td s; length bs = size_td_struct st;
  wf_fd_struct st; wf_desc_struct st; wf_size_desc_struct st\<rbrakk> \<Longrightarrow>
   access_ti_struct st v bs ! i = access_ti s v (take (size_td s) (drop n bs)) ! (i - n)"

"\<lbrakk>field_lookup_list ts f m = Some (s, m + n); n \<le> i; i < n + size_td s; length bs = size_td_list ts;
  wf_fd_list ts; wf_desc_list ts; wf_size_desc_list ts\<rbrakk> \<Longrightarrow>
   access_ti_list ts v bs ! i = access_ti s v (take (size_td s) (drop n bs)) ! (i - n)"

"\<lbrakk>field_lookup_tuple x f m = Some (s, m + n); n \<le> i; i < n + size_td s; length bs = size_td_tuple x;
  wf_fd_tuple x; wf_desc_tuple x; wf_size_desc_tuple x\<rbrakk> \<Longrightarrow>
   access_ti_tuple x v bs ! i = access_ti s v (take (size_td s) (drop n bs)) ! (i - n)"
proof (induct t and st and ts and x arbitrary: f m n i s bs v and f m n i s bs v and f m n i s bs v and f m n i s bs v)
case (TypDesc algn st nm)
  then show ?case by (auto split: if_split_asm)
next
  case (TypScalar sz algn d)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto
  from Cons_typ_desc.prems obtain
    lbs: "length bs = size_td_tuple x + size_td_list fs" and
    wf_fd_x: "wf_fd_tuple (DTuple d nm y)" and
    wf_desc_x: "wf_desc_tuple (DTuple d nm y)" and
    wf_fd_fs: "wf_fd_list fs" and
    wf_size_desc_x: "wf_size_desc_tuple (DTuple d nm y)" and
    wf_size_desc_fs: "wf_size_desc_list fs" and
    nm_notin:  "nm \<notin> dt_snd ` set fs" and
    wf_desc_fs: "wf_desc_list fs" and
    i_lower: "n \<le> i" and
    i_upper: "i < n + size_td s"
    by (auto simp add: x)

  from lbs
  have lbs_drop: "length (drop (size_td_tuple x) bs) = size_td_list fs"
    by simp

  from lbs
  have lbs_take: "length (take (size_td_tuple x) bs) = size_td_tuple (DTuple d nm y)"
    by (simp add: x)

  from lbs wf_fd_x
  have eq1: "length (access_ti d v (take (size_td d) bs)) = size_td d"
    by (metis lbs_take length_fa_ti size_td_tuple.simps wf_fd_tuple.simps x)

  from Cons_typ_desc.prems obtain f1 fxs
    where f: "f = f1#fxs"
    by (cases f) auto

  thm Cons_typ_desc.hyps [simplified x]

  show ?case
  proof (cases "f1 = nm")
    case True
    show ?thesis
    proof (cases "field_lookup d fxs m")
      case None
      from Cons_typ_desc.prems field_lookup_list_None [OF nm_notin]
      have False
        by (simp add: True None f x)
      thus ?thesis by simp
    next
      case (Some r)
      from Cons_typ_desc.prems have r: "r = (s, m + n)"
        by (simp add: x True Some f)
      hence fl: "field_lookup_tuple (DTuple d nm y) f m = Some (s, m + n)"
        by  (simp add: f True Some r)
      from td_set_wf_size_desc(4)[OF wf_size_desc_x td_set_tuple_field_lookup_tupleD, OF fl]
      have "wf_size_desc s" .
      from wf_size_desc_gt(1)[OF this]
      have "0 < size_td s" .


      with td_set_tuple_offset_size_m [OF td_set_tuple_field_lookup_tupleD, OF fl]
      have n_le: "n < size_td d"
        by auto

      have i_in_d: "i < size_td d"
        using \<open>size_td s + (m + n - m) \<le> size_td_tuple (DTuple d nm y)\<close> i_upper by auto
      have bound: "size_td s + (m + n - m) \<le> size_td_tuple (DTuple d nm y)" by fact
      from bound
      have take_eq: "(take (size_td s) (drop n (take (size_td d) bs))) =
         (take (size_td s) (drop n bs))"
        by (simp add: take_drop)
      from  Cons_typ_desc.hyps(1)[simplified x, OF fl i_lower i_upper lbs_take wf_fd_x wf_desc_x wf_size_desc_x, of v] lbs bound
      show ?thesis
        by (simp add: x True Some r take_eq eq1 nth_append i_in_d)
    qed
  next
    case False
    with Cons_typ_desc.prems
    have fl: "field_lookup_list fs (f1 # fxs) (m + size_td d) = Some (s, m + n)"
      by (clarsimp simp add: x f False)
    hence n_bound: "size_td d \<le> n"
      by (meson field_lookup_offset_le(3) nat_add_left_cancel_le)

    from fl
    have fl: "field_lookup_list fs (f1 # fxs) (m + size_td d) = Some (s, (m + size_td d) + (n - size_td d))"
      by (metis Nat.diff_cancel field_lookup_list_offset2 field_lookup_list_offsetD)
    from n_bound
    have take_eq: "(take (size_td s) (drop (n - size_td d + size_td d) bs)) =
            (take (size_td s) (drop n bs))"
      by simp

    have i_lower': "n - size_td d \<le> i - size_td d"
      using diff_le_mono i_lower by blast

    have i_upper': "i - size_td d < n - size_td d + size_td s"
      using i_lower i_upper by linarith

    have i_notin_d: "\<not> i < size_td d"
      by (meson i_lower leD less_le_trans n_bound)

    from Cons_typ_desc.hyps(2) [OF fl i_lower' i_upper' lbs_drop wf_fd_fs wf_desc_fs wf_size_desc_fs, where v=v]
      False n_bound
    show ?thesis
      by (simp add: x f eq1 nth_append i_notin_d)
  qed
next
  case (DTuple_typ_desc d nm y)
then show ?case apply (cases f) by (auto split: if_split_asm)
qed

lemma field_lookup_nth_focus:
 "\<lbrakk>field_lookup t f 0 = Some (s, n); n \<le> i; i < n + size_td s; length bs = size_td t;
  wf_fd t; wf_desc t; wf_size_desc t\<rbrakk> \<Longrightarrow>
   access_ti t v bs ! i = access_ti s v (take (size_td s) (drop n bs)) ! (i - n)"
  using field_lookup_nth_focus' [where m=0] by auto


lemma field_lookup_nth_update_focus':
  fixes t::"('a, 'b) typ_info"
  and st::"('a, 'b) typ_info_struct"
  and ts::"('a, 'b) typ_info_tuple list"
  and x::"('a, 'b) typ_info_tuple"
shows
"\<lbrakk>field_lookup t f m = Some (s, m + n); n \<le> i; i < n + size_td s; length bs = size_td t;
  wf_fd t; wf_desc t; wf_size_desc t\<rbrakk> \<Longrightarrow>
   access_ti t v (bs[i := b]) =
    super_update_bs (access_ti s v ((take (size_td s) (drop n bs))[i - n := b]))
     (access_ti t v bs) n"

"\<lbrakk>field_lookup_struct st f m = Some (s, m + n); n \<le> i; i < n + size_td s; length bs = size_td_struct st;
  wf_fd_struct st; wf_desc_struct st; wf_size_desc_struct st\<rbrakk> \<Longrightarrow>
   access_ti_struct st v (bs[i := b]) =
     super_update_bs (access_ti s v ((take (size_td s) (drop n bs))[i - n := b]))
      (access_ti_struct st v bs) n"

"\<lbrakk>field_lookup_list ts f m = Some (s, m + n); n \<le> i; i < n + size_td s; length bs = size_td_list ts;
  wf_fd_list ts; wf_desc_list ts; wf_size_desc_list ts\<rbrakk> \<Longrightarrow>
   access_ti_list ts v (bs[i := b]) =
     super_update_bs (access_ti s v ((take (size_td s) (drop n bs))[i - n := b]))
       (access_ti_list ts v bs) n"

"\<lbrakk>field_lookup_tuple x f m = Some (s, m + n); n \<le> i; i < n + size_td s; length bs = size_td_tuple x;
  wf_fd_tuple x; wf_desc_tuple x; wf_size_desc_tuple x\<rbrakk> \<Longrightarrow>
   access_ti_tuple x v (bs[i := b]) =
     super_update_bs (access_ti s v ((take (size_td s) (drop n bs))[i - n := b]))
       (access_ti_tuple x v bs) n"
proof (induct t and st and ts and x arbitrary: f m n i s bs v and f m n i s bs v and f m n i s bs v and f m n i s bs v)
case (TypDesc algn st nm)
  then show ?case
    by (auto split: if_split_asm simp add: super_update_bs_def)
       (metis TypDesc.prems(4) TypDesc.prems(5) access_ti.simps le_refl length_fa_ti length_list_update)
next
  case (TypScalar sz algn d)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto
  from Cons_typ_desc.prems obtain
    lbs: "length bs = size_td_tuple x + size_td_list fs" and
    wf_fd_x: "wf_fd_tuple (DTuple d nm y)" and
    wf_desc_x: "wf_desc_tuple (DTuple d nm y)" and
    wf_fd_fs: "wf_fd_list fs" and
    wf_size_desc_x: "wf_size_desc_tuple (DTuple d nm y)" and
    wf_size_desc_fs: "wf_size_desc_list fs" and
    nm_notin:  "nm \<notin> dt_snd ` set fs" and
    wf_desc_fs: "wf_desc_list fs" and
    i_lower: "n \<le> i" and
    i_upper: "i < n + size_td s"
    by (auto simp add: x)

  from lbs
  have lbs_drop: "length (drop (size_td_tuple x) bs) = size_td_list fs"
    by simp

  from lbs
  have lbs_take: "length (take (size_td_tuple x) bs) = size_td_tuple (DTuple d nm y)"
    by (simp add: x)

  from lbs wf_fd_x
  have eq1: "length (access_ti d v (take (size_td d) bs)) = size_td d"
    by (metis lbs_take length_fa_ti size_td_tuple.simps wf_fd_tuple.simps x)

  from Cons_typ_desc.prems obtain f1 fxs
    where f: "f = f1#fxs"
    by (cases f) auto

  thm Cons_typ_desc.hyps [simplified x]

  show ?case
  proof (cases "f1 = nm")
    case True
    show ?thesis
    proof (cases "field_lookup d fxs m")
      case None
      from Cons_typ_desc.prems field_lookup_list_None [OF nm_notin]
      have False
        by (simp add: True None f x)
      thus ?thesis by simp
    next
      case (Some r)
      from Cons_typ_desc.prems have r: "r = (s, m + n)"
        by (simp add: x True Some f)
      hence fl: "field_lookup_tuple (DTuple d nm y) f m = Some (s, m + n)"
        by  (simp add: f True Some r)
      from td_set_wf_size_desc(4)[OF wf_size_desc_x td_set_tuple_field_lookup_tupleD, OF fl]
      have "wf_size_desc s" .
      from wf_size_desc_gt(1)[OF this]
      have "0 < size_td s" .


      with td_set_tuple_offset_size_m [OF td_set_tuple_field_lookup_tupleD, OF fl]
      have n_le: "n < size_td d"
        by auto

      have i_in_d: "i < size_td d"
        using \<open>size_td s + (m + n - m) \<le> size_td_tuple (DTuple d nm y)\<close> i_upper by auto
      have bound: "size_td s + (m + n - m) \<le> size_td_tuple (DTuple d nm y)" by fact
      from bound
      have take_eq: "(take (size_td s) (drop n (take (size_td d) bs))) =
         (take (size_td s) (drop n bs))"
        by (simp add: take_drop)
      from bound
      have take_upd_eq: " ((take (size_td d) bs)[i := b]) = (take (size_td d) (bs[i := b]))"
        by (simp add: take_update_swap)

      have take_eq1: "take (size_td s) (drop n (take (size_td d) bs)) = take (size_td s) (drop n bs)"
        using take_eq by blast

      have l_take_s: "length (take (size_td s) (drop n bs)) = size_td s"
        using bound lbs_take by auto

      have sz_s: "size_td s \<le> length bs - n"
        using l_take_s by auto

      from fl
      have fd_cons_s: "fd_cons s"
        using wf_fd_consD wf_fd_field_lookup(4) wf_fd_x by blast
      have l_acc_s: "length (access_ti s v ((take (size_td s) (drop n bs))[i - n := b])) = size_td s"
        by (simp add: fd_cons_length [OF fd_cons_s] sz_s eq1)

      have take_eq2: "(take (size_td s) (drop n (take (size_td d) bs)))[i - n := b] = (take (size_td s) (drop n bs))[i - n := b]"
        using take_eq1 by presburger

      note hyp =  Cons_typ_desc.hyps(1)[simplified x, OF fl i_lower i_upper lbs_take wf_fd_x wf_desc_x wf_size_desc_x, of v,
          simplified, simplified x, simplified, simplified take_upd_eq]
      from lbs bound
      show ?thesis
        apply (simp add: x True Some r take_eq take_upd_eq eq1 list_update_append i_in_d)
        apply (simp add: hyp)
        apply (subst super_update_bs_append1)
         apply (simp add: l_acc_s eq1)
        apply (simp add: take_eq2)
        done
    qed
  next
    case False
    with Cons_typ_desc.prems
    have fl: "field_lookup_list fs (f1 # fxs) (m + size_td d) = Some (s, m + n)"
      by (clarsimp simp add: x f False)
    hence n_bound: "size_td d \<le> n"
      by (meson field_lookup_offset_le(3) nat_add_left_cancel_le)

    from fl
    have fl: "field_lookup_list fs (f1 # fxs) (m + size_td d) = Some (s, (m + size_td d) + (n - size_td d))"
      by (metis Nat.diff_cancel field_lookup_list_offset2 field_lookup_list_offsetD)
    from n_bound
    have take_eq: "(take (size_td s) (drop (n - size_td d + size_td d) bs)) =
            (take (size_td s) (drop n bs))"
      by simp

    have i_lower': "n - size_td d \<le> i - size_td d"
      using diff_le_mono i_lower by blast

    have i_upper': "i - size_td d < n - size_td d + size_td s"
      using i_lower i_upper by linarith

    have i_notin_d: "\<not> i < size_td d"
      by (meson i_lower leD less_le_trans n_bound)

    from i_notin_d have take_d_eq: "take (size_td d) (bs[i := b]) = take (size_td d) bs"
      by simp
    have drop_shift: "(drop (size_td d) bs)[i - size_td d := b] = drop (size_td d) (bs[i := b])"
      by (metis drop_update_swap i_notin_d le_def)

    note hyp = Cons_typ_desc.hyps(2) [OF fl i_lower' i_upper' lbs_drop wf_fd_fs wf_desc_fs wf_size_desc_fs, where v=v,
        simplified x, simplified, simplified drop_shift]
    from  False n_bound
    show ?thesis
      apply (simp add: x f eq1 nth_append i_notin_d)
      apply (subst super_update_bs_append2)
       apply (simp add: eq1)
      apply (simp add: take_d_eq add: eq1)
      apply (simp add: hyp)
      done
  qed
next
  case (DTuple_typ_desc d nm y)
then show ?case apply (cases f) by (auto split: if_split_asm)
qed

lemma field_lookup_nth_update_focus:
shows
"\<lbrakk>field_lookup t f 0 = Some (s, n); n \<le> i; i < n + size_td s; length bs = size_td t;
  wf_fd t; wf_desc t; wf_size_desc t\<rbrakk> \<Longrightarrow>
   access_ti t v (bs[i := b]) =
    super_update_bs (access_ti s v ((take (size_td s) (drop n bs))[i - n := b]))
     (access_ti t v bs) n"
  using field_lookup_nth_update_focus' [where m=0] by auto


context mem_type
begin
lemma mem_type_field_lookup_access_ti_take_drop:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
  assumes lbs : "length bs = size_of TYPE('a)"
  shows "access_ti s v (take (size_td s) (drop n bs)) =
           take (size_td s) (drop n (access_ti (typ_info_t TYPE('a)) v bs))"
proof -
  have wf_fd: "wf_fd (typ_info_t TYPE('a))"
    by (simp add: wf_fdp_fdD wf_lf_fdp)
  have wf_desc: "wf_desc (typ_info_t TYPE('a))" by simp
  have wf_size: "wf_size_desc (typ_info_t TYPE('a))" by simp
  from field_lookup_access_ti_take_drop [OF fl wf_fd wf_desc wf_size lbs [simplified size_of_def]]
  show ?thesis .
qed

lemma mem_type_update_ti_super_update_bs:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
  assumes lbs: "length bs = size_of TYPE('a)"
  assumes lv: "length v = size_td s"
  shows "update_ti s v (update_ti (typ_info_t TYPE('a)) bs w) =
           update_ti (typ_info_t TYPE('a)) (super_update_bs v bs n) w"
proof -
  have wf_fd: "wf_fd (typ_info_t TYPE('a))"
    by (simp add: wf_fdp_fdD wf_lf_fdp)
  have lsuper: "length (super_update_bs v bs n) = size_td (typ_info_t TYPE('a))"
    by (metis add.commute field_lookup_offset_size' fl lbs length_super_update_bs local.size_of_def lv)

  from fi_fu_consistentD [OF fl wf_fd lbs [simplified size_of_def] lv, of w] lbs
  show ?thesis
    by (simp add: update_ti_t_def lsuper lv size_of_def)
qed


lemma mem_type_update_ti_from_bytes_super_update_bs:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
  assumes lbs: "length bs = size_of TYPE('a)"
  assumes lv: "length v = size_td s"
  shows "update_ti s v (from_bytes bs) = update_ti (typ_info_t TYPE('a)) (super_update_bs v bs n) undefined"
proof -
  from mem_type_update_ti_super_update_bs [OF fl lbs lv, of undefined]
  show ?thesis
    by (simp add: from_bytes_def update_ti_t_def lbs size_of_def)
qed

lemma mem_type_field_lookup_nth_focus:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
  assumes i_lower: "n \<le> i"
  assumes i_upper: "i < n + size_td s"
  assumes lbs : "length bs = size_of TYPE('a)"
  shows "access_ti (typ_info_t TYPE('a)) v bs ! i =
           access_ti s v (take (size_td s) (drop n bs)) ! (i - n)"
proof -
  have wf_fd: "wf_fd (typ_info_t TYPE('a))"
    by (simp add: wf_fdp_fdD wf_lf_fdp)
  have wf_desc: "wf_desc (typ_info_t TYPE('a))" by simp
  have wf_size: "wf_size_desc (typ_info_t TYPE('a))" by simp
  from field_lookup_nth_focus [OF fl i_lower i_upper lbs [simplified size_of_def] wf_fd wf_desc wf_size]
  show ?thesis .
qed

lemma mem_type_field_lookup_nth_update_focus:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
  assumes i_lower: "n \<le> i"
  assumes i_upper: "i < n + size_td s"
  assumes lbs : "length bs = size_of TYPE('a)"
  shows
"access_ti (typ_info_t TYPE('a)) v (bs[i := b]) =
    super_update_bs (access_ti s v ((take (size_td s) (drop n bs))[i - n := b]))
     (access_ti (typ_info_t TYPE('a)) v bs) n"
proof -
  have wf_fd: "wf_fd (typ_info_t TYPE('a))"
    by (simp add: wf_fdp_fdD wf_lf_fdp)
  have wf_desc: "wf_desc (typ_info_t TYPE('a))" by simp
  have wf_size: "wf_size_desc (typ_info_t TYPE('a))" by simp
  from field_lookup_nth_update_focus [OF fl i_lower i_upper lbs [simplified size_of_def] wf_fd wf_desc wf_size]
  show ?thesis .
qed
end



ML \<open>@{term  "xs[i := v]"}\<close>


lemma nth_take_drop_index_shift:
"n \<le> i \<Longrightarrow> i < m + n \<Longrightarrow> m + n \<le> length xs \<Longrightarrow> take m (drop n xs) ! (i - n) = xs ! i"
proof (induct xs arbitrary: n i m)
  case Nil
  then show ?case by simp
next
  case (Cons x1 xs)
  then show ?case by auto
qed

lemma super_update_bs_update_index_shift: "n \<le> i \<Longrightarrow> i - n < length bs \<Longrightarrow> n + length bs \<le> length xbs \<Longrightarrow>
(super_update_bs bs xbs n)[i := b] = super_update_bs (bs[i - n := b]) xbs n"
  apply (simp add: super_update_bs_def)
  apply (simp add: list_update_append)
  done

lemma super_update_bs_nth_shift:
 "n \<le> i \<Longrightarrow> i - n < length bs \<Longrightarrow> n + length bs \<le> length xbs \<Longrightarrow> super_update_bs bs xbs n ! i = bs ! (i - n)"
  apply (simp add: super_update_bs_def)
  apply (simp add: nth_append)
  done

lemma (in mem_type) field_lookup_is_padding_byte_outer_to_inner:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
  assumes lower_bound_x: "n \<le> x"
  assumes upper_bound_x: "x < n + size_td s"
  assumes is_padding: "padding_base.is_padding_byte (access_ti (typ_info_t (TYPE('a)))) (update_ti (typ_info_t (TYPE('a)))) (size_td (typ_info_t (TYPE('a)))) x"
  shows "padding_base.is_padding_byte (access_ti s) (update_ti s) (size_td s) (x - n)"
proof (rule padding_base.is_padding_byteI)
  from lower_bound_x upper_bound_x show "x - n < size_td s" by simp
next
  fix v::'a and bs::"byte list"
  assume "x - n < size_td s"
  assume lbs: "length bs = size_td s"
  from fl have sz: "size_td s + n \<le> size_of TYPE('a)"
    by (simp add: field_lookup_offset_size' size_of_def)

  obtain pfx sfx xbs where
    xbs: "xbs = pfx @ bs @ sfx" and
    lpfx: "length pfx = n" and
    lsfx: "length sfx = size_of TYPE('a) - n - size_td s"
    by (metis Ex_list_of_length)
  with sz have lxbs: "length xbs = size_of TYPE('a)"
    by (metis add_leD2 add_le_imp_le_diff lbs le_add_diff_inverse length_append)
  from xbs lpfx lsfx xbs lbs have bs: "(take (size_td s) (drop n xbs)) = bs"
    by simp

  have bound: "x - n < size_td s" by fact

  have lacc: "length (access_ti (typ_info_t TYPE('a)) v xbs) = size_of TYPE('a)"
    by (simp add: length_fa_ti lxbs size_of_def)

  from mem_type_field_lookup_access_ti_take_drop [OF fl lxbs, simplified bs, of v]
  have acc_conv: "access_ti s v bs =
         take (size_td s) (drop n (access_ti (typ_info_t TYPE('a)) v xbs))" .
  from padding_base.is_padding_byte_acc_eq [OF is_padding, of xbs v] lxbs
  have "access_ti (typ_info_t TYPE('a)) v xbs ! x = xbs ! x"
    by (simp add: size_of_def)
  moreover have "xbs ! x = bs ! (x - n)"
    using xbs lpfx lsfx lxbs bound
    apply (simp add: xbs)
    by (metis bs drop_append_miracle le_def lower_bound_x nth_append nth_take xbs)
  moreover have "take (size_td s) (drop n (access_ti (typ_info_t TYPE('a)) v xbs)) ! (x - n) =
    access_ti (typ_info_t TYPE('a)) v xbs ! x"
    using lacc lxbs bound lower_bound_x upper_bound_x
    by (metis less_diff_conv2 nth_take_drop_index_shift sz)

  ultimately show "access_ti s v bs ! (x - n) = bs ! (x - n)"
    by (simp add: acc_conv)
next
  fix v::'a and bs::"byte list" and b::byte
  assume "x - n < size_td s"
  assume lbs: "length bs = size_td s"

  from fl have sz: "size_td s + n \<le> size_of TYPE('a)"
    by (simp add: local.field_lookup_offset_size local.size_of_def)

  obtain pfx sfx xbs where
    xbs: "xbs = pfx @ bs @ sfx" and
    lpfx: "length pfx = n" and
    lsfx: "length sfx = size_of TYPE('a) - n - size_td s"
    by (metis Ex_list_of_length)

  with sz have lxbs: "length xbs = size_of TYPE('a)"
    by (metis add_leD2 add_le_imp_le_diff lbs le_add_diff_inverse length_append)
  from xbs lpfx lsfx xbs lbs have bs: "(take (size_td s) (drop n xbs)) = bs"
    by simp

  have v_upd_conv: "(update_ti (typ_info_t TYPE('a)) (to_bytes v xbs) v) = v"
    by (simp add: fu_fa length_fa_ti local.size_of_def local.to_bytes_def lxbs update_ti_update_ti_t)

   have lxto: "length (to_bytes v xbs) = size_of TYPE('a)"
     by (simp add: length_fa_ti lxbs size_of_def to_bytes_def)

  from lxto lbs
  have lsuper: "length (super_update_bs bs (to_bytes v xbs) n) = size_of TYPE('a)"
    using sz by auto

  have bound: "x - n < size_td s" by fact

  have xbs_super: "xbs = super_update_bs bs xbs n"
    by (simp add: lpfx super_update_bs_def xbs)
  from mem_type_update_ti_super_update_bs [OF fl lxto lbs, of v, simplified v_upd_conv]
  have upd_eq1:
    "update_ti s bs v =
       update_ti (typ_info_t TYPE('a)) (super_update_bs bs (to_bytes v xbs) n) v" .

  have lbs': "length (bs[x - n := b]) = size_td s"
    using lbs by auto

  from mem_type_update_ti_super_update_bs [OF fl lxto lbs', of v, simplified v_upd_conv]
  have upd_eq2:
    "update_ti s (bs[x - n := b]) v =
       update_ti (typ_info_t TYPE('a)) (super_update_bs (bs[x - n := b]) (to_bytes v xbs) n) v" .

  from lxto lxbs lbs lower_bound_x upper_bound_x bound sz
  have super_eq: "(super_update_bs bs (to_bytes v xbs) n)[x := b] = super_update_bs (bs[x - n := b]) (to_bytes v xbs) n"
    by (simp add: super_update_bs_update_index_shift)

  from padding_base.is_padding_byte_upd_eq [OF is_padding, of "(super_update_bs bs (to_bytes v xbs) n)" v b] lsuper
  have upd_pad: "update_ti (typ_info_t TYPE('a)) (super_update_bs bs (to_bytes v xbs) n) v =
         update_ti (typ_info_t TYPE('a)) ((super_update_bs bs (to_bytes v xbs) n)[x := b]) v"
    by (simp add: size_of_def)
  show "update_ti s bs v = update_ti s (bs[x - n := b]) v"
    apply (simp add: upd_eq1)
    apply (simp add: upd_pad)
    apply (simp add: upd_eq2)
    apply (simp add: super_eq)
    done
qed

lemma (in mem_type) field_lookup_is_padding_byte_inner_to_outer:
  assumes fl: "field_lookup (typ_info_t (TYPE('a))) f 0 = Some (s, n)"
  assumes lower_bound_x: "n \<le> x"
  assumes upper_bound_x: "x < n + size_td s"
  assumes is_padding: "padding_base.is_padding_byte (access_ti s) (update_ti s) (size_td s) (x - n)"
  shows "padding_base.is_padding_byte (access_ti (typ_info_t (TYPE('a)))) (update_ti (typ_info_t (TYPE('a)))) (size_td (typ_info_t (TYPE('a)))) x"
proof (rule padding_base.is_padding_byteI)
  from lower_bound_x upper_bound_x fl
  show "x < size_td (typ_info_t TYPE('a))"
    using field_lookup_offset_size' by fastforce
next
  fix v::'a and bs::"byte list"
  assume sz: "x < size_td (typ_info_t TYPE('a))"
  assume lbs: "length bs = size_td (typ_info_t TYPE('a))"
  from mem_type_field_lookup_nth_focus [OF fl lower_bound_x upper_bound_x, simplified size_of_def, OF lbs]
  have eq1:
    "access_ti (typ_info_t TYPE('a)) v bs ! x =
       access_ti s v (take (size_td s) (drop n bs)) ! (x - n)" .
  from lbs fl
  have l_take_drop: "length (take (size_td s) (drop n bs)) = size_td s"
    using field_lookup_offset_size' by fastforce

  from padding_base.is_padding_byte_acc_eq [OF is_padding l_take_drop, of v]
  have eq2:
    "access_ti s v (take (size_td s) (drop n bs)) ! (x - n) =
      take (size_td s) (drop n bs) ! (x - n)" .
  have eq3:
    "take (size_td s) (drop n bs) ! (x - n) = bs ! x"
    by (metis add.commute field_lookup_offset_size' fl lbs lower_bound_x nth_take_drop_index_shift upper_bound_x)

  show "access_ti (typ_info_t TYPE('a)) v bs ! x = bs ! x"
    apply (simp add: eq1)
    apply (simp add: eq2)
    apply (simp add: eq3)
    done
next
  fix v::'a and bs::"byte list" and b::byte
  assume sz: "x < size_td (typ_info_t TYPE('a))"
  assume lbs: "length bs = size_td (typ_info_t TYPE('a))"

  have v_upd_conv: "(update_ti (typ_info_t TYPE('a)) (to_bytes v bs) v) = v"
    by (simp add: fu_fa lbs length_fa_ti to_bytes_def update_ti_update_ti_t)

  have lto: "length (to_bytes v bs) = size_td (typ_info_t TYPE('a))"
    by (simp add: lbs length_fa_ti to_bytes_def)

  note upd_focus = mem_type_update_ti_super_update_bs [OF fl, simplified size_of_def, OF lto, where w=v, simplified v_upd_conv]

  from lbs lower_bound_x upper_bound_x sz
  have lbs1: "length (take (size_td s) (drop n bs)) = size_td s"
    by (metis add_le_imp_le_diff field_lookup_offset_size' fl length_drop length_take min.absorb2)

  from lbs lower_bound_x upper_bound_x
  have bs_upd_eq: "(take (size_td s) (drop n bs))[x - n := b] = take (size_td s) (drop n (bs[x := b]))"
    by (metis drop_update_swap take_update_swap)

  from lbs lbs1 lower_bound_x upper_bound_x
  have lbs2: "length (take (size_td s) (drop n (bs[x := b]))) = size_td s"
    by (metis bs_upd_eq length_list_update)


  from lbs lbs1
  have bs_super_conv: "(super_update_bs (take (size_td s) (drop n bs)) bs n) = bs"
    by (metis append_take_drop_id super_update_bs_def take_drop_append)

  from lbs lbs1 lower_bound_x upper_bound_x
  have bs_upd_super_conv: "(super_update_bs (take (size_td s) (drop n (bs[x := b]))) bs n) = bs[x := b]"
    by (metis add.commute bs_super_conv bs_upd_eq field_lookup_offset_size' fl
        nat_diff_less super_update_bs_update_index_shift)

  from mem_type_update_ti_super_update_bs [OF fl, simplified size_of_def, OF lbs lbs1, simplified bs_super_conv, where w=v]
  have eq1:
    "update_ti (typ_info_t TYPE('a)) bs v =
       update_ti s (take (size_td s) (drop n bs)) (update_ti (typ_info_t TYPE('a)) bs v)" by simp

  from mem_type_update_ti_super_update_bs [OF fl, simplified size_of_def, OF lbs lbs2, simplified bs_upd_super_conv, where w=v]
  have eq2:
    "update_ti s (take (size_td s) (drop n (bs[x := b])))
       (update_ti (typ_info_t TYPE('a)) bs v) =
     update_ti (typ_info_t TYPE('a)) (bs[x := b]) v" .

  thm upd_focus [OF lbs1]
  note pad_eq= padding_base.is_padding_byte_upd_eq [OF is_padding, OF lbs1, where b=b]
  show "update_ti (typ_info_t TYPE('a)) bs v =
          update_ti (typ_info_t TYPE('a)) (bs[x := b]) v"
    apply (subst eq1)
    apply (simp add: pad_eq)
    apply (simp add: bs_upd_eq)
    apply (simp add: eq2)
    done
qed


lemma (in mem_type) field_lookup_is_padding_byte:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
  assumes lower_bound_x: "n \<le> x"
  assumes upper_bound_x: "x < n + size_td s"
  shows
   "padding_base.is_padding_byte (access_ti s) (update_ti s) (size_td s) (x - n) \<longleftrightarrow>
    padding_base.is_padding_byte
     (access_ti (typ_info_t (TYPE('a)))) (update_ti (typ_info_t (TYPE('a)))) (size_td (typ_info_t (TYPE('a)))) x"
  using field_lookup_is_padding_byte_outer_to_inner [OF fl lower_bound_x upper_bound_x]
    field_lookup_is_padding_byte_inner_to_outer [OF fl lower_bound_x upper_bound_x]
  by blast

lemma (in mem_type) field_lookup_is_value_byte_outer_to_inner:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
  assumes lower_bound_x: "n \<le> x"
  assumes upper_bound_x: "x < n + size_td s"
  assumes is_value: "padding_base.is_value_byte (access_ti (typ_info_t (TYPE('a)))) (update_ti (typ_info_t (TYPE('a)))) (size_td (typ_info_t (TYPE('a)))) x"
  shows "padding_base.is_value_byte (access_ti s) (update_ti s) (size_td s) (x - n)"
proof (rule padding_base.is_value_byteI)
  from lower_bound_x upper_bound_x show "x - n < size_td s" by simp
next
  fix v::'a and bs::"byte list" and bs'::"byte list"
  assume "x - n < size_td s"
  assume lbs: "length bs = size_td s"
  assume lbs': "length bs' = size_td s"
  from fl have sz: "size_td s + n \<le> size_of TYPE('a)"
    by (metis (no_types, lifting) diff_add_zero diff_is_0_eq dual_order.trans field_lookup_offset_size' size_of_def)

  obtain pfx sfx xbs where
    xbs: "xbs = pfx @ bs @ sfx" and
    lpfx: "length pfx = n" and
    lsfx: "length sfx = size_of TYPE('a) - n - size_td s"
    by (metis Ex_list_of_length)

  with sz have lxbs: "length xbs = size_of TYPE('a)"
    by (metis add_leD2 add_le_imp_le_diff lbs le_add_diff_inverse length_append)
  from xbs lpfx lsfx xbs lbs have bs: "(take (size_td s) (drop n xbs)) = bs"
    by simp

  obtain pfx' sfx' xbs' where
    xbs': "xbs' = pfx' @ bs' @ sfx'" and
    lpfx': "length pfx' = n" and
    lsfx': "length sfx' = size_of TYPE('a) - n - size_td s"
    by (metis Ex_list_of_length)

  with sz have lxbs': "length xbs' = size_of TYPE('a)"
    by (metis add_leD2 add_le_imp_le_diff lbs' le_add_diff_inverse length_append)

  from xbs' lpfx' lsfx' xbs' lbs' have bs': "(take (size_td s) (drop n xbs')) = bs'"
    by simp

  have bound: "x - n < size_td s" by fact

  have lacc: "length (access_ti (typ_info_t TYPE('a)) v xbs) = size_of TYPE('a)"
    by (simp add: fd_cons_length lxbs size_of_def wf_fd_consD)

  have v_upd_conv: "(update_ti (typ_info_t TYPE('a)) (to_bytes v xbs) v) = v"
    by (simp add: fu_fa lacc lxbs size_of_def to_bytes_def update_ti_update_ti_t)

  have lxto: "length (to_bytes v xbs) = size_of TYPE('a)"
    by (simp add: lacc to_bytes_def)

  from lxto lbs
  have lsuper: "length (super_update_bs bs (to_bytes v xbs) n) = size_of TYPE('a)"
    using sz by auto

  have bound: "x - n < size_td s" by fact

  have xbs_super: "xbs = super_update_bs bs xbs n"
    by (simp add: lpfx super_update_bs_def xbs)

  from mem_type_update_ti_super_update_bs [OF fl lxto lbs, of v, simplified v_upd_conv]
  have upd_eq1:
    "update_ti s bs v =
       update_ti (typ_info_t TYPE('a)) (super_update_bs bs (to_bytes v xbs) n) v" .

  have idx_shift1:
    "take (size_td s) (drop n
         (access_ti (typ_info_t TYPE('a))
           (update_ti (typ_info_t TYPE('a)) (super_update_bs bs (to_bytes v xbs) n) v) xbs'))
        ! (x - n)
       = access_ti (typ_info_t TYPE('a))
           (update_ti (typ_info_t TYPE('a)) (super_update_bs bs (to_bytes v xbs) n) v) xbs'
        ! x "
    by (metis bound fd_cons_length less_diff_conv2 local.wf_fd lower_bound_x lxbs'
        nth_take_drop_index_shift size_of_def sz wf_fd_consD)

  from lxto lbs lower_bound_x upper_bound_x sz
  have super_nth: "super_update_bs bs (to_bytes v xbs) n ! x = bs ! (x - n)"
    by (simp add: super_update_bs_nth_shift)
  note val_eq = padding_base.is_value_byte_acc_upd_cancel [OF is_value lsuper [simplified size_of_def] lxbs' [simplified size_of_def]]
  note acc_eq = mem_type_field_lookup_access_ti_take_drop [OF fl lxbs', simplified bs' ]
  show "access_ti s (update_ti s bs v) bs' ! (x - n) = bs ! (x - n)"
    apply (simp add: upd_eq1)
    apply (simp add: acc_eq)
    apply (simp add: idx_shift1 )
    apply (simp add: val_eq)
    apply (simp add: super_nth)
    done
next
  fix v::'a and bs::"byte list" and b::"byte"
  assume "x - n < size_td s"
  assume lbs: "length bs = size_td s"


  from fl have sz: "size_td s + n \<le> size_of TYPE('a)"
    by (metis (no_types, lifting) diff_add_zero diff_is_0_eq dual_order.trans field_lookup_offset_size' size_of_def)

  obtain pfx sfx xbs where
    xbs: "xbs = pfx @ bs @ sfx" and
    lpfx: "length pfx = n" and
    lsfx: "length sfx = size_of TYPE('a) - n - size_td s"
    by (metis Ex_list_of_length)

  with sz have lxbs: "length xbs = size_of TYPE('a)"
    by (metis add_leD2 add_le_imp_le_diff lbs le_add_diff_inverse length_append)
  from xbs lpfx lsfx xbs lbs have bs: "(take (size_td s) (drop n xbs)) = bs"
    by simp

  obtain xbs' where
    xbs': "xbs' = pfx @ bs [x - n := b] @ sfx" by blast
  from lxbs lbs xbs have lxbs': "length xbs' = size_of TYPE('a)"
    using xbs' by auto
  from xbs' lpfx lxbs' lbs have bs': "(take (size_td s) (drop n xbs')) = bs[x - n :=b]"
    by simp

  from lbs lower_bound_x upper_bound_x sz lpfx lsfx
  have xbs'_conv: "xbs' = xbs[x := b]"
    by (simp add: xbs xbs' list_update_append)

  note eq1 = mem_type_field_lookup_access_ti_take_drop [OF fl lxbs, simplified bs, of v]
  note eq2 = mem_type_field_lookup_access_ti_take_drop [OF fl lxbs', simplified bs', of v]
  note val_eq = padding_base.is_value_byte_acc_eq [OF is_value lxbs [simplified size_of_def], where b=b]
  show "access_ti s v bs = access_ti s v (bs[x - n := b])"
    apply (simp add: eq1)
    apply (simp add: val_eq)
    apply (simp add: eq2)
    apply (simp add: xbs'_conv)
    done
qed

lemma (in mem_type) field_lookup_is_value_byte_inner_to_outer:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
  assumes lower_bound_x: "n \<le> x"
  assumes upper_bound_x: "x < n + size_td s"
  assumes is_value: "padding_base.is_value_byte (access_ti s) (update_ti s) (size_td s) (x - n)"
  shows "padding_base.is_value_byte (access_ti (typ_info_t (TYPE('a)))) (update_ti (typ_info_t (TYPE('a)))) (size_td (typ_info_t (TYPE('a)))) x"
proof (rule padding_base.is_value_byteI)
  from lower_bound_x upper_bound_x fl
  show "x < size_td (typ_info_t TYPE('a))"
    using field_lookup_offset_size' by fastforce
next
  fix v::'a and bs::"byte list" and bs'::"byte list"
  assume sz: "x < size_td (typ_info_t TYPE('a))"
  assume lbs: "length bs = size_td (typ_info_t TYPE('a))"
  assume lbs': "length bs' = size_td (typ_info_t TYPE('a))"

  from fl have sz: "size_td s + n \<le> size_of TYPE('a)"
    by (metis (no_types, lifting) diff_add_zero diff_is_0_eq dual_order.trans field_lookup_offset_size' size_of_def)

  from sz lbs
  have super_bs: "(super_update_bs (take (size_td s) (drop n bs)) bs n) = bs"
    by (metis (no_types, lifting) append.assoc append_len2 append_take_drop_id diff_diff_cancel
        length_drop nat_move_sub_le size_of_def super_update_bs_def take_add)
  from lower_bound_x upper_bound_x lbs sz
  have l_take_drop: "length (take (size_td s) (drop n bs)) = size_td s"
    by (simp add: size_of_def)

  from lower_bound_x upper_bound_x lbs' sz
  have l_take_drop': "length (take (size_td s) (drop n bs')) = size_td s"
    by (simp add: size_of_def)

  from lbs lower_bound_x upper_bound_x sz
  have take_drop_eq: "take (size_td s) (drop n bs) ! (x - n) = bs ! x"
    by (simp add: size_of_def)


  note upd_focus = mem_type_update_ti_super_update_bs [OF fl, simplified size_of_def, OF lbs l_take_drop, simplified super_bs, symmetric ]
  note acc_focus = mem_type_field_lookup_nth_focus [OF fl lower_bound_x upper_bound_x, simplified size_of_def, OF lbs']
  note cancel = padding_base.is_value_byte_acc_upd_cancel [OF is_value l_take_drop l_take_drop']
  show "access_ti (typ_info_t TYPE('a)) (update_ti (typ_info_t TYPE('a)) bs v) bs' ! x =
         bs ! x"
    apply (subst upd_focus)
    apply (simp add: acc_focus)
    apply (simp add: cancel)
    apply (simp add: take_drop_eq)
    done
next
  fix v::'a and bs::"byte list" and b::"byte"
  assume sz: "x < size_td (typ_info_t TYPE('a))"
  assume lbs: "length bs = size_td (typ_info_t TYPE('a))"

  from fl have sz: "size_td s + n \<le> size_of TYPE('a)"
    by (metis (no_types, lifting) diff_add_zero diff_is_0_eq dual_order.trans field_lookup_offset_size' size_of_def)

  note eq1 = mem_type_field_lookup_access_ti_take_drop [OF fl, simplified size_of_def, OF lbs ]


  from sz lower_bound_x upper_bound_x lbs
  have l_take_s: "length (take (size_td s) (drop n bs)) = size_td s"
    by (simp add: size_of_def)

  from lbs sz lower_bound_x upper_bound_x
  have super_eq:
    "super_update_bs (access_ti s v (take (size_td s) (drop n bs)))
          (access_ti (typ_info_t TYPE('a)) v bs) n = (access_ti (typ_info_t TYPE('a)) v bs)"
    by (metis append_take_drop_id eq1 l_take_s length_drop length_fa_ti
        length_take local.wf_fd super_update_bs_def take_drop_append)

  note focus1 = mem_type_field_lookup_nth_update_focus [OF fl lower_bound_x upper_bound_x, simplified size_of_def, OF lbs]
  note pad_eq = padding_base.is_value_byte_acc_eq [OF is_value l_take_s, symmetric]
  show "access_ti (typ_info_t TYPE('a)) v bs =
         access_ti (typ_info_t TYPE('a)) v (bs[x := b])"

    apply (simp add: focus1)
    apply (subst pad_eq)
    apply (simp add: super_eq)
    done
qed


lemma (in mem_type) field_lookup_is_value_byte:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
  assumes lower_bound_x: "n \<le> x"
  assumes upper_bound_x: "x < n + size_td s"
  shows "padding_base.is_value_byte (access_ti s) (update_ti s) (size_td s) (x - n) \<longleftrightarrow>
   padding_base.is_value_byte (access_ti (typ_info_t (TYPE('a))))
     (update_ti (typ_info_t (TYPE('a)))) (size_td (typ_info_t (TYPE('a)))) x"
  using field_lookup_is_value_byte_inner_to_outer [OF fl lower_bound_x upper_bound_x]
    field_lookup_is_value_byte_outer_to_inner [OF fl lower_bound_x upper_bound_x]
  by blast

thm padding_base.eq_padding_def
thm padding_base.eq_upto_padding_def
(* Such a thing is not present! *)



lemma td_set_component_descs_independent:
 fixes t::"'a xtyp_info"
  and st::"'a xtyp_info_struct"
  and ts::"'a xtyp_info_tuple list"
  and x::"'a xtyp_info_tuple"
shows
  "(s, n) \<in> td_set t m \<Longrightarrow> component_descs_independent t \<Longrightarrow> component_descs_independent s"
  "(s, n) \<in> td_set_struct st m \<Longrightarrow> component_descs_independent_struct st \<Longrightarrow> component_descs_independent s"
  "(s, n) \<in> td_set_list ts m \<Longrightarrow> component_descs_independent_list ts \<Longrightarrow> component_descs_independent s"
  "(s, n) \<in> td_set_tuple x m \<Longrightarrow> component_descs_independent_tuple x \<Longrightarrow> component_descs_independent s"
proof (induct t and st and ts and x arbitrary: m and m and m and m)
case (TypDesc algn st nm)
then show ?case by auto
next
  case (TypScalar sz algn d)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  then show ?case by auto
next
  case (DTuple_typ_desc d nm y)
  then show ?case by auto
qed

lemma td_set_wf_component_descs:
 fixes t::"'a xtyp_info"
  and st::"'a xtyp_info_struct"
  and ts::"'a xtyp_info_tuple list"
  and x::"'a xtyp_info_tuple"
shows
  "(s, n) \<in> td_set t m \<Longrightarrow> wf_component_descs t \<Longrightarrow> wf_component_descs s"
  "(s, n) \<in> td_set_struct st m \<Longrightarrow> wf_component_descs_struct st \<Longrightarrow> wf_component_descs s"
  "(s, n) \<in> td_set_list ts m \<Longrightarrow> wf_component_descs_list ts \<Longrightarrow> wf_component_descs s"
  "(s, n) \<in> td_set_tuple x m \<Longrightarrow> wf_component_descs_tuple x \<Longrightarrow> wf_component_descs s"
proof (induct t and st and ts and x arbitrary: m and m and m and m)
case (TypDesc algn st nm)
then show ?case by auto
next
  case (TypScalar sz algn d)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  then show ?case by auto
next
  case (DTuple_typ_desc d nm y)
  then show ?case by auto
qed


lemma td_set_field_descs:
 fixes t::"'a xtyp_info"
  and st::"'a xtyp_info_struct"
  and ts::"'a xtyp_info_tuple list"
  and x::"'a xtyp_info_tuple"
shows
  "(s, n) \<in> td_set t m \<Longrightarrow> wf_component_descs t \<Longrightarrow> component_desc s \<in> insert (component_desc t) (set (field_descs t))"
  "(s, n) \<in> td_set_struct st m \<Longrightarrow> wf_component_descs_struct st \<Longrightarrow> component_desc s \<in> (set (field_descs_struct st))"
  "(s, n) \<in> td_set_list ts m \<Longrightarrow> wf_component_descs_list ts \<Longrightarrow> component_desc s \<in> (set (field_descs_list ts))"
  "(s, n) \<in> td_set_tuple x m \<Longrightarrow> wf_component_descs_tuple x \<Longrightarrow> component_desc s \<in> (set (field_descs_tuple x))"
proof (induct t and st and ts and x arbitrary: m and m and m and m)
case (TypDesc algn st nm)
then show ?case by auto
next
  case (TypScalar sz algn d)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  then show ?case by auto
next
  case (DTuple_typ_desc d nm y)
  then show ?case by auto
qed

lemma td_set_wf_field_descs:
 fixes t::"'a xtyp_info"
  and st::"'a xtyp_info_struct"
  and ts::"'a xtyp_info_tuple list"
  and x::"'a xtyp_info_tuple"
shows
  "(s, n) \<in> td_set t m \<Longrightarrow> wf_field_descs (set (field_descs t)) \<Longrightarrow> wf_field_descs (set (field_descs s))"
  "(s, n) \<in> td_set_struct st m \<Longrightarrow>wf_field_descs (set (field_descs_struct st)) \<Longrightarrow> wf_field_descs (set (field_descs s))"
  "(s, n) \<in> td_set_list ts m \<Longrightarrow> wf_field_descs (set (field_descs_list ts)) \<Longrightarrow> wf_field_descs (set (field_descs s))"
  "(s, n) \<in> td_set_tuple x m \<Longrightarrow> wf_field_descs (set (field_descs_tuple x)) \<Longrightarrow> wf_field_descs (set (field_descs s))"
proof (induct t and st and ts and x arbitrary: m and m and m and m)
case (TypDesc algn st nm)
then show ?case by auto
next
  case (TypScalar sz algn d)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  then show ?case by auto
next
  case (DTuple_typ_desc d nm y)
  then show ?case by auto
qed

context xmem_type
begin
lemma xmem_type_td_set_field_descs:
  "(s,n) \<in> td_set (typ_info_t TYPE('a)) m \<Longrightarrow>
  component_desc s \<in> insert (component_desc (typ_info_t TYPE('a))) (set (field_descs (typ_info_t TYPE('a))))"
  using td_set_field_descs local.wf_component_descs by blast

lemma field_lookup_component_desc:
"field_lookup (typ_info_t TYPE('a)) f m = Some (s, n) \<Longrightarrow>
  component_desc s \<in> insert (component_desc (typ_info_t TYPE('a))) (set (field_descs (typ_info_t TYPE('a))))"
  using xmem_type_td_set_field_descs td_set_field_lookupD
  by blast

lemma field_lookup_wf_field_desc:
"field_lookup (typ_info_t TYPE('a)) f m = Some (s, n) \<Longrightarrow>
  wf_field_desc (component_desc s)"
  using field_lookup_component_desc
  by (meson local.wf_field_descs' wf_field_descs_def)

lemma field_lookup_component_descs_independent:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f m = Some (s, n)"
  shows "component_descs_independent s"
  using field_lookup_component_desc [OF fl]
  by (meson fl local.component_descs_independent td_set_component_descs_independent(1) td_set_field_lookupD)

lemma field_lookup_wf_component_descs:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f m = Some (s, n)"
  shows "wf_component_descs s"
  using field_lookup_component_desc [OF fl] td_set_wf_component_descs fl
    local.wf_component_descs td_set_field_lookupD by blast

lemma field_lookup_wf_field_descs:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f m = Some (s, n)"
  shows "wf_field_descs (set (field_descs s))"
  using td_set_wf_field_descs fl local.wf_field_descs td_set_field_lookupD by blast


lemma field_lookup_field_access_access_ti:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f m = Some (s, n)"
  shows "field_access (component_desc s) = access_ti s"
  using access_ti_component_desc_compatible(1) [OF field_lookup_wf_component_descs [OF fl]
      field_lookup_component_descs_independent [OF fl]  field_lookup_wf_field_descs [OF fl]]
  by (simp add: fun_eq_iff)

lemma field_lookup_field_update_update_ti:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f m = Some (s, n)"
  shows "field_update (component_desc s) = update_ti s"
  using update_ti_component_desc_compatible(1) [OF field_lookup_wf_component_descs [OF fl]
      field_lookup_component_descs_independent [OF fl]  field_lookup_wf_field_descs [OF fl]]
  by (simp add: fun_eq_iff)

lemma field_lookup_field_sz_size_td:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f m = Some (s, n)"
  shows "field_sz (component_desc s) = size_td s"
  using size_td_field_sz(1)  [OF field_lookup_wf_component_descs [OF fl] ]
  by simp

lemma field_lookup_component_desc_complement_padding:
"field_lookup (typ_info_t TYPE('a)) f m = Some (s, n) \<Longrightarrow>
  complement_padding (field_access (component_desc s)) (field_update (component_desc s)) (field_sz (component_desc s))"
  using field_lookup_component_desc
  by (meson field_lookup_wf_field_desc padding_lense.axioms(1) wf_field_desc.axioms)


lemma field_lookup_component_desc_complement_padding':
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f m = Some (s, n)"
  shows "complement_padding (access_ti s) (update_ti s) (size_td s)"
  using field_lookup_component_desc_complement_padding
    field_lookup_field_access_access_ti [OF fl]
    field_lookup_field_update_update_ti [OF fl]
    field_lookup_field_sz_size_td [OF fl]
  by (metis fl)

lemma field_lookup_padding_lense:
"field_lookup (typ_info_t TYPE('a)) f m = Some (s, n) \<Longrightarrow>
  padding_lense (access_ti s) (update_ti s) (size_td s)"
  by (metis field_lookup_field_access_access_ti field_lookup_field_update_update_ti
      field_lookup_wf_component_descs field_lookup_wf_field_desc size_td_field_sz(1) wf_field_desc_def)

sublocale lense: padding_lense
  "access_ti (typ_info_t TYPE('a))"
  "update_ti (typ_info_t TYPE('a))"
  "size_of TYPE('a)"
  using local.field_access_access_ti local.field_sz_size_of
    local.field_update_update_ti local.xmem_type_wf_field_desc.padding_lense_axioms by simp

end


lemma eq_padding_access_update_field_cancel:
  assumes fl: "field_lookup (typ_info_t (TYPE('a::xmem_type))) f 0 = Some (s, n)"
  assumes lower_bound_x: "n \<le> x"
  assumes upper_bound_x: "x < n + size_of TYPE('b)"
  assumes match: "export_uinfo s = typ_uinfo_t TYPE('b::xmem_type)"
  assumes lbs: "length bs = size_of TYPE('b)"
  assumes lbs': "length bs' = size_of TYPE('a)"
  assumes eq_padding: "padding_base.eq_padding (access_ti s) (size_td s) bs (take (size_of TYPE('b)) (drop n bs'))"
  shows "access_ti (typ_info_t TYPE('a::xmem_type)) (update_ti s bs v) bs' ! x = bs ! (x - n)"
proof -
  obtain i where i: "i = x - n" by blast
  from match fl have sz_b: "size_of TYPE('b) = size_td s"
    using export_size_of by blast

  interpret cps: complement_padding "access_ti s" "update_ti s" "size_td s"
    by (rule field_lookup_component_desc_complement_padding' [OF fl])

  from lower_bound_x upper_bound_x sz_b
  have x_n_bound: "x - n < size_td s"
    by simp
  from eq_padding
  have l_take_drop_bs': "length (take (size_td s) (drop n bs')) = size_td s"
    by (metis lbs padding_base.eq_padding_length_eq sz_b)

  from lower_bound_x upper_bound_x fl lbs'
  have acc_bs': "take (size_td s) (drop n bs') ! (x - n) = bs' ! x"
    by (metis add.commute field_lookup_offset_size nth_take_drop_index_shift size_of_def sz_b)

  from mem_type_field_lookup_nth_focus [OF fl lower_bound_x [simplified size_of_def] upper_bound_x [simplified sz_b] lbs']
  have "access_ti (typ_info_t TYPE('a)) (update_ti s bs v) bs' ! x =
     access_ti s (update_ti s bs v) (take (size_td s) (drop n bs')) ! (x - n) " .
  also have "\<dots> = bs ! (x - n)" (is "?lhs = ?rhs")
  proof (cases "padding_base.is_padding_byte (access_ti s) (update_ti s) (size_td s) (x - n)")
    case True

    from padding_base.is_padding_byte_acc_eq [OF True l_take_drop_bs' ] acc_bs'
    have "?lhs = bs' ! x" by simp
    also have "bs' ! x = bs ! (x - n)"
      using cps.eq_padding_padding_byte_id [OF eq_padding True] acc_bs' sz_b
      by simp
    finally show ?thesis .
  next
    case False
    then have is_value: "cps.is_value_byte (x - n)" using cps.complement x_n_bound by simp
    from cps.is_value_byte_acc_upd_cancel [OF is_value lbs [simplified sz_b] l_take_drop_bs']
    show ?thesis .
  qed
  finally show ?thesis .
qed

context xmem_type
begin

sublocale xmem_type_padding: complement_padding
  "access_ti (typ_info_t TYPE('a))"
  "update_ti (typ_info_t TYPE('a))"
  "size_of TYPE('a)"
  using xmem_type_wf_field_desc.complement_padding_axioms
  by (simp add: field_access_access_ti field_update_update_ti field_sz_size_td size_of_def)
end

lemma drop_heap_list_le2:
  "heap_list h n (x + of_nat k)
      = drop k (heap_list h (n + k) x)"
  by (simp add: drop_heap_list_le)

lemma heap_list_take_drop:
  assumes N_bound: "unat a + N \<le> 2 ^ len_of TYPE(addr_bitsize)"
  shows "n + m \<le> N \<Longrightarrow> take m (drop n (heap_list hp N a)) =
       heap_list hp m (a + word_of_nat n)"
  apply (induct m arbitrary: n)
   apply simp
  apply simp
  using N_bound
  by auto
    (metis (no_types, opaque_lifting) add.left_commute add.right_neutral add_Suc_right drop_heap_list_le2 heap_list_rec take_drop take_heap_list_le)

lemma heap_list_take_drop':
  assumes N_bound: "unat a + N \<le> addr_card"
  assumes bound: "n + m \<le> N"
  shows "take m (drop n (heap_list hp N a)) =
       heap_list hp m (a + word_of_nat n)"
proof -
  have "addr_card = 2 ^ len_of TYPE(addr_bitsize)"
    by (simp add: addr_card)
  from heap_list_take_drop [OF N_bound [simplified this ] bound] show ?thesis by blast
qed

experiment
  fixes proj:: "'a::xmem_type \<Rightarrow> 'b::xmem_type"
  fixes t::"'a xtyp_info"

  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n)"
  and     eu: "export_uinfo t = typ_uinfo_t TYPE('b)"
  assumes access_comp: "access_ti t v = access_ti (typ_info_t TYPE('b)) (proj v)"
  assumes surj: "surj proj"
begin

lemma sz: "size_td t = size_of TYPE('b)"
  using eu
  by (metis export_uinfo_size size_of_def typ_uinfo_size)

lemma "padding_base.eq_padding (access_ti t) (size_td t) =
       padding_base.eq_padding (access_ti (typ_info_t TYPE('b))) (size_of TYPE('b))"
  unfolding padding_base.eq_padding_def
  apply (rule ext)
  apply (rule ext)
  apply (simp add: sz)
  apply (simp add: access_comp)
  using surj
  by (metis surj_def)
end



definition is_padding_byte::"typ_uinfo \<Rightarrow> nat \<Rightarrow> bool" where
  "is_padding_byte t i \<equiv> i < size_td t \<and>
     (\<forall>bs b. length bs = size_td t \<longrightarrow> norm_tu t (bs[i := b]) = norm_tu t bs)"

definition is_value_byte::"typ_uinfo \<Rightarrow> nat \<Rightarrow> bool" where
  "is_value_byte t i \<equiv> i < size_td t \<and>
     (\<exists>bs b. length bs = size_td t \<and> norm_tu t (bs[i := b]) \<noteq> norm_tu t bs)"

lemma is_padding_byteI:
  assumes "i < size_td t"
  assumes "\<And>i bs b. length bs = size_td t \<Longrightarrow> norm_tu t (bs[i := b]) = norm_tu t bs"
  shows "is_padding_byte t i"
  using assms by (simp add: is_padding_byte_def)

lemma complement_tu_padding:
"i < size_td t \<Longrightarrow> is_padding_byte t i \<noteq> is_value_byte t i"
  by (auto simp add: is_padding_byte_def is_value_byte_def)

definition eq_padding::"typ_uinfo \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> bool" where
 "eq_padding t bs bs' \<equiv> length bs = size_td t \<and> length bs' = size_td t \<and>
    (\<forall>i. is_padding_byte t i \<longrightarrow> bs ! i = bs' ! i)"

definition eq_upto_padding::"typ_uinfo \<Rightarrow> byte list \<Rightarrow> byte list \<Rightarrow> bool" where
 "eq_upto_padding t bs bs' \<equiv> length bs = size_td t \<and> length bs' = size_td t \<and>
    (\<forall>i. is_value_byte t i \<longrightarrow> bs ! i = bs' ! i)"

lemma eq_padding_refl[simp]: "length bs = size_td t \<Longrightarrow> eq_padding t bs bs"
  by (auto simp add: eq_padding_def)

lemma eq_upto_padding_refl[simp]: "length bs = size_td t \<Longrightarrow> eq_upto_padding t bs bs"
  by (auto simp add: eq_upto_padding_def)

lemma eq_padding_sym: "eq_padding t bs bs' \<longleftrightarrow> eq_padding t bs' bs"
  by (auto simp add: eq_padding_def)

lemma eq_padding_symp: "symp (eq_padding t)"
  by (simp add: symp_def eq_padding_sym)

lemma eq_upto_padding_sym: "eq_upto_padding t bs bs' \<longleftrightarrow> eq_upto_padding t bs' bs"
  by (auto simp add: eq_upto_padding_def)

lemma eq_upto_padding_symp: "symp (eq_upto_padding t)"
  by (simp add: symp_def eq_upto_padding_sym)

lemma eq_padding_trans: "eq_padding t bs1 bs2 \<Longrightarrow> eq_padding t bs2 bs3 \<Longrightarrow> eq_padding t bs1 bs3"
  by (auto simp add: eq_padding_def)

lemma eq_padding_transp: "transp (eq_padding t)"
  unfolding transp_def
  by (auto intro: eq_padding_trans)

lemma eq_upto_padding_trans: "eq_upto_padding t bs1 bs2 \<Longrightarrow> eq_upto_padding t bs2 bs3 \<Longrightarrow> eq_upto_padding t bs1 bs3"
  by (auto simp add: eq_upto_padding_def)

lemma eq_upto_padding_transp: "transp (eq_upto_padding t)"
  unfolding transp_def
  by (auto intro: eq_upto_padding_trans)

lemma eq_padding_eq_upto_padding_eq: "eq_padding t bs bs' \<Longrightarrow> eq_upto_padding t bs bs' \<Longrightarrow> bs = bs'"
proof -
assume a1: "eq_padding t bs bs'"
assume a2: "eq_upto_padding t bs bs'"
  have f3: "length bs' = size_td t"
    using a1 by (simp add: eq_padding_def)
  have "length bs = size_td t"
    using a1 eq_padding_def by blast
    then show ?thesis
      using f3 a2 a1 by (metis (full_types) complement_tu_padding eq_padding_def eq_upto_padding_def nth_equalityI)
qed

thm padding_base.is_padding_byte_def




lemma is_padding_byte_access_ti':
  fixes t::"'a xtyp_info"
  and st::"'a xtyp_info_struct"
  and ts::"'a xtyp_info_tuple list"
  and x::"'a xtyp_info_tuple"
shows
"\<lbrakk> wf_desc t; wf_size_desc t; wf_field_descs (set (field_descs t)); wf_component_descs t; wf_fd t;
  i < size_td t; length bs = size_td t;
   \<forall>bs b. length bs = size_td t \<longrightarrow> norm_tu (map_td field_norm (\<lambda>_. ()) t) (bs[i := b]) = norm_tu (export_uinfo t) bs\<rbrakk>
  \<Longrightarrow> access_ti t v bs ! i = bs ! i"

"\<lbrakk> wf_desc_struct st; wf_size_desc_struct st; wf_field_descs (set (field_descs_struct st));
  wf_component_descs_struct st;  wf_fd_struct st; i < size_td_struct st; length bs = size_td_struct st;
   \<forall>bs b. length bs = size_td_struct st \<longrightarrow> norm_tu_struct (map_td_struct field_norm (\<lambda>_. ()) st) (bs[i := b]) = norm_tu_struct ((map_td_struct field_norm (\<lambda>_. ()) st)) bs\<rbrakk>
  \<Longrightarrow> access_ti_struct st v bs ! i = bs ! i"

"\<lbrakk> wf_desc_list ts; wf_size_desc_list ts; wf_field_descs (set (field_descs_list ts));
  wf_component_descs_list ts; wf_fd_list ts;  i < size_td_list ts; length bs = size_td_list ts;
   \<forall>bs b. length bs = size_td_list ts \<longrightarrow> norm_tu_list (map_td_list field_norm (\<lambda>_. ()) ts) (bs[i := b]) = norm_tu_list ((map_td_list field_norm (\<lambda>_. ()) ts)) bs\<rbrakk>
  \<Longrightarrow> access_ti_list ts v bs ! i = bs ! i"

"\<lbrakk> wf_desc_tuple x; wf_size_desc_tuple x; wf_field_descs (set (field_descs_tuple x));
  wf_component_descs_tuple x; wf_fd_tuple x;  i < size_td_tuple x; length bs = size_td_tuple x;
   \<forall>bs b. length bs = size_td_tuple x \<longrightarrow> norm_tu_tuple (map_td_tuple field_norm (\<lambda>_. ()) x) (bs[i := b]) = norm_tu_tuple ((map_td_tuple field_norm (\<lambda>_. ()) x)) bs\<rbrakk>
  \<Longrightarrow> access_ti_tuple x v bs ! i = bs ! i"
proof (induct t and st and ts and x arbitrary:  bs i and bs i and bs i and bs i)
case (TypDesc algn st nm)
then show ?case by auto
next
  case (TypScalar sz algn d)
  from TypScalar obtain
    wf_d: "wf_field_desc d" and
    field_sz: "field_sz d =sz" and
    i_bound: "i < sz" and
    lbs: "length bs = sz" and
    padding: "\<And>bs b. length bs = sz \<Longrightarrow>
         field_norm sz algn d (bs[i := b]) = field_norm sz algn d bs"
    by simp

  interpret wf: wf_field_desc d by (rule wf_d)
  show ?case
  proof (cases "wf.is_padding_byte i")
    case True
    then show ?thesis
      using field_sz lbs wf.is_padding_byte_acc_id by auto
  next
    case False
    note not_padding = this
    with wf.complement field_sz i_bound have is_value: "wf.is_value_byte i" by blast
    from is_value padding have False
      by (auto simp add: field_norm_def)
        (metis (mono_tags, opaque_lifting) field_sz i_bound list_update_id not_padding padding_base.is_value_byte_upd_neq
          wf.access_result_size wf.is_padding_byte_def wf.update_access wf.update_access_unequal)
    then show ?thesis by blast
  qed
next
case (TypAggregate ts)
then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto
  from Cons_typ_desc.prems obtain
    wf_desc_d: "wf_desc d" and
    wf_fd_x: "wf_fd_tuple (DTuple d nm y)" and
    wf_fd_d: "wf_fd d" and
    wf_fd_fs: "wf_fd_list fs" and
    nm_notin: "nm \<notin> dt_snd ` set fs" and
    wf_desc_fs: "wf_desc_list fs" and
    wf_sz_d: "wf_size_desc d" and
    wf_sz_fs: "wf_size_desc_list fs" and
    wf_field_d: "wf_field_desc (component_desc d)" and
    wf_fields_d: "wf_field_descs (set (field_descs d))" and
    wf_fields_fs: "wf_field_descs (set (field_descs_list fs))" and
    y: "y = component_desc d" and
    wf_comp_d: "wf_component_descs d" and
    wf_comp_fs: "wf_component_descs_list fs" and
    i_bound:"i < size_td d + size_td_list fs" and
    lbs: "length bs = size_td d + size_td_list fs" and
    wf_desc_x: "wf_desc_tuple x" and
    wf_sz_x: "wf_size_desc_tuple x" and
    wf_decs_x: "wf_field_descs (set (field_descs_tuple x))" and
    wf_comp_x: "wf_component_descs_tuple x" and

    padding: "\<And>bs b . length bs = size_td d + size_td_list fs \<Longrightarrow>
          norm_tu (map_td field_norm (\<lambda>_. ()) d)
               (take (size_td d) (bs[i := b])) @
              norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs)
               (drop (size_td d) (bs[i := b])) =
              norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) bs) @
              norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs)
               (drop (size_td d) bs)"
    by (auto simp add: x)

  have padding_d: "\<forall>bs. length bs = size_td d \<longrightarrow>
     (\<forall>b. norm_tu (map_td field_norm (\<lambda>_. ()) d) (bs[i := b]) =
          norm_tu (map_td field_norm (\<lambda>_. ()) d) bs)"
  proof (safe)
    fix bs::"byte list" and b::"byte"
    assume lbs: "length bs = size_td d"
    from lbs obtain xbs sfx where xbs: "xbs = bs @ sfx" and lxbs: "length xbs = size_td d + size_td_list fs"
      by (metis Ex_list_of_length length_append)

    from lbs
    have eq1: "(take (size_td d) ((bs @ sfx)[i := b])) = bs[i := b]" by (simp add: list_update_append)

    from lbs
    have lbs': "length (bs[i:=b]) = size_td d" by simp

    from wf_fd_norm_tu(1)[rule_format, OF wf_fd_d lbs ] lbs
    have lnorm1:"length (norm_tu (map_td field_norm (\<lambda>_. ()) d) bs) = size_td d"
      by (simp add: export_uinfo_def length_fa_ti wf_fd_d)

    from wf_fd_norm_tu(1)[rule_format, OF wf_fd_d lbs' ] lbs'
    have lnorm2: "length (norm_tu (map_td field_norm (\<lambda>_. ()) d) (bs[i:=b])) = size_td d"
      by (simp add: export_uinfo_def length_fa_ti wf_fd_d)

    from padding [OF lxbs, of b] xbs lbs
    show "norm_tu (map_td field_norm (\<lambda>_. ()) d) (bs[i := b]) =
       norm_tu (map_td field_norm (\<lambda>_. ()) d) bs"
      apply simp
      apply (subst (asm) list_append_eq_split_conv)
       apply (simp add: eq1 lnorm1 lnorm2)
      apply (simp add: eq1)
      done
  qed


  from lbs
  have lbs_drop: "length (drop (size_td d) bs) = size_td_list fs"
    by (simp add: x)

  from lbs
  have lbs_take: "length (take (size_td d) bs) = size_td d"
    by (simp add: x)

  have lacc: "length (access_ti d v (take (size_td d) bs)) = size_td d"
    by (metis lbs_take length_fa_ti size_td_tuple.simps wf_fd_tuple.simps wf_fd_x x)

  show ?case

  proof (cases "i < size_td d")
    case True
    note hyp = Cons_typ_desc.hyps(1) [OF wf_desc_x wf_sz_x wf_decs_x wf_comp_x, simplified x, OF wf_fd_x, simplified, OF True lbs_take padding_d]
    from hyp lbs
    show ?thesis
      by (simp add: x True nth_append lacc )
  next
    case False
    from False i_bound have i_bound': "i - size_td d  < size_td_list fs" by simp
    have padding_fs: "\<forall>bs b.
      length bs = size_td_list fs \<longrightarrow>
      norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) (bs[i - size_td d := b]) =
      norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) bs"
    proof (safe)
      fix bs::"byte list" and b::"byte"
      assume lbs: "length bs = size_td_list fs"
      from lbs obtain xbs pfx where xbs: "xbs = pfx @ bs" and lxbs: "length xbs = size_td d + size_td_list fs"
        and lpfx: "length pfx = size_td d"
        by (metis Ex_list_of_length length_append)

      from lpfx
      have drop_eq1: "drop (size_td d) xbs = bs"
        by (simp add: xbs)
      from lpfx False have drop_eq2: "(drop (size_td d) (xbs[i := b])) = bs [i - size_td d := b]"
        by (auto simp add: xbs list_update_append)
      from lpfx False
      have take_eq1: "take (size_td d) (xbs[i := b]) = pfx"
        by (simp add: xbs list_update_append)
      from lpfx False
      have take_eq2: "take (size_td d) xbs = pfx"
        by (simp add: xbs)

      have leq1: "length (norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) (xbs[i := b]))) = size_td d"
        apply (simp add: take_eq1)
        using wf_fd_norm_tu(1)[rule_format, OF wf_fd_d lpfx ] lpfx
        by (simp add: export_uinfo_def length_fa_ti wf_fd_d)
      have leq2: "length (norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) xbs)) = size_td d"
        apply (simp add: take_eq2)
        using wf_fd_norm_tu(1)[rule_format, OF wf_fd_d lpfx ] lpfx
        by (simp add: export_uinfo_def length_fa_ti wf_fd_d)

      from padding [OF lxbs, of b, simplified drop_eq1 drop_eq2]
      show "norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) (bs[i - size_td d := b]) =
      norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) bs"
        apply -
        apply (subst (asm) list_append_eq_split_conv)
        apply (simp add: leq1 leq2)
        apply simp
        done
    qed
    from False lbs have drop_eq: "drop (size_td d) bs ! (i - size_td d) = bs ! i" by simp
    note hyp = Cons_typ_desc.hyps(2) [OF wf_desc_fs wf_sz_fs wf_fields_fs wf_comp_fs wf_fd_fs i_bound' lbs_drop padding_fs]
    from hyp
    show ?thesis by (simp add: x False nth_append lacc drop_eq)
  qed
next
  case (DTuple_typ_desc d nm y)
  then show ?case by (auto simp add: export_uinfo_def)
qed

lemma is_padding_byte_access_ti:
  assumes wf: "wf_desc (t::'a xtyp_info)"
  and wf_sz: "wf_size_desc t"
  and wf_descs: "wf_field_descs (set (field_descs t))"
  and wf_comp: "wf_component_descs t"
  and wf_fd: "wf_fd t"
  and i_bound: "i < size_td t"
  and lbs: "length bs = size_td t"
  and is_padding: "is_padding_byte (export_uinfo t) i"
shows "access_ti t v bs ! i = bs ! i"
  using is_padding_byte_access_ti'(1) [OF wf wf_sz wf_descs wf_comp wf_fd i_bound lbs] is_padding
  by (simp add: is_padding_byte_def export_uinfo_def)

context xmem_type
begin
lemma xmem_type_is_padding_byte_access_ti:
  assumes padding: "is_padding_byte (typ_uinfo_t TYPE('a)) i"
  and i_bound: "i < size_of TYPE('a)"
  and lbs: "length bs = size_of TYPE('a)"
shows "access_ti (typ_info_t TYPE('a)) v bs ! i = bs ! i"
proof -
  have wf: "wf_desc (typ_info_t TYPE('a))" by simp
  have wf_sz: "wf_size_desc (typ_info_t TYPE('a))" by simp
  have wf_descs: "wf_field_descs (set (field_descs (typ_info_t TYPE('a))))"
    using local.wf_field_descs by blast
  have wf_comp: "wf_component_descs (typ_info_t TYPE('a))"
    by (simp add: local.wf_component_descs)
  have wf_fd: "wf_fd (typ_info_t TYPE('a))"
    using local.wf_desc local.wf_lf wf_fdp_fd(1) wf_lf_fdp by blast
  from is_padding_byte_access_ti [OF wf wf_sz wf_descs wf_comp wf_fd
      i_bound [simplified size_of_def] lbs [simplified size_of_def]
      padding [simplified typ_uinfo_t_def]]
  show ?thesis .
qed




end

lemma is_padding_byte_update_ti_id':
  fixes t::"'a xtyp_info"
  and st::"'a xtyp_info_struct"
  and ts::"'a xtyp_info_tuple list"
  and x::"'a xtyp_info_tuple"
shows
"\<lbrakk> wf_desc t; wf_size_desc t; wf_field_descs (set (field_descs t)); wf_component_descs t; wf_fd t;
  i < size_td t; length bs = size_td t;
   \<forall>bs b. length bs = size_td t \<longrightarrow> norm_tu (map_td field_norm (\<lambda>_. ()) t) (bs[i := b]) = norm_tu (export_uinfo t) bs\<rbrakk>
  \<Longrightarrow> update_ti t (bs[i := b]) v = update_ti t bs v"

"\<lbrakk> wf_desc_struct st; wf_size_desc_struct st; wf_field_descs (set (field_descs_struct st));
  wf_component_descs_struct st;  wf_fd_struct st; i < size_td_struct st; length bs = size_td_struct st;
   \<forall>bs b. length bs = size_td_struct st \<longrightarrow> norm_tu_struct (map_td_struct field_norm (\<lambda>_. ()) st) (bs[i := b]) = norm_tu_struct ((map_td_struct field_norm (\<lambda>_. ()) st)) bs\<rbrakk>
  \<Longrightarrow> update_ti_struct st (bs[i := b]) v = update_ti_struct st bs v"

"\<lbrakk> wf_desc_list ts; wf_size_desc_list ts; wf_field_descs (set (field_descs_list ts));
  wf_component_descs_list ts; wf_fd_list ts;  i < size_td_list ts; length bs = size_td_list ts;
   \<forall>bs b. length bs = size_td_list ts \<longrightarrow> norm_tu_list (map_td_list field_norm (\<lambda>_. ()) ts) (bs[i := b]) = norm_tu_list ((map_td_list field_norm (\<lambda>_. ()) ts)) bs\<rbrakk>
  \<Longrightarrow> update_ti_list ts (bs[i := b]) v = update_ti_list ts bs v"

"\<lbrakk> wf_desc_tuple x; wf_size_desc_tuple x; wf_field_descs (set (field_descs_tuple x));
  wf_component_descs_tuple x; wf_fd_tuple x;  i < size_td_tuple x; length bs = size_td_tuple x;
   \<forall>bs b. length bs = size_td_tuple x \<longrightarrow> norm_tu_tuple (map_td_tuple field_norm (\<lambda>_. ()) x) (bs[i := b]) = norm_tu_tuple ((map_td_tuple field_norm (\<lambda>_. ()) x)) bs\<rbrakk>
  \<Longrightarrow> update_ti_tuple x (bs[i := b]) v = update_ti_tuple x bs v"
proof (induct t and st and ts and x arbitrary:  bs i v and bs i v and bs i v and bs i v)
case (TypDesc algn st nm)
then show ?case by auto
next
  case (TypScalar sz algn d)
  from TypScalar obtain
    wf_d: "wf_field_desc d" and
    field_sz: "field_sz d =sz" and
    i_bound: "i < sz" and
    lbs: "length bs = sz" and
    padding: "\<And>bs b. length bs = sz \<Longrightarrow>
         field_norm sz algn d (bs[i := b]) = field_norm sz algn d bs"
    by simp

  interpret wf: wf_field_desc d by (rule wf_d)
  show ?case
  proof (cases "wf.is_padding_byte i")
    case True
    then show ?thesis
      using field_sz lbs wf.is_padding_byte_upd_eq by auto
  next
    case False
    note not_padding = this
    with wf.complement field_sz i_bound have is_value: "wf.is_value_byte i" by blast
    from is_value padding have False
      by (auto simp add: field_norm_def)
        (metis (mono_tags, opaque_lifting) field_sz i_bound list_update_id not_padding padding_base.is_value_byte_upd_neq
          wf.access_result_size wf.is_padding_byte_def wf.update_access wf.update_access_unequal)
    then show ?thesis by blast
  qed
next
case (TypAggregate ts)
then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto
  from Cons_typ_desc.prems obtain
    wf_desc_d: "wf_desc d" and
    wf_fd_x: "wf_fd_tuple (DTuple d nm y)" and
    wf_fd_d: "wf_fd d" and
    wf_fd_fs: "wf_fd_list fs" and
    nm_notin: "nm \<notin> dt_snd ` set fs" and
    wf_desc_fs: "wf_desc_list fs" and
    wf_sz_d: "wf_size_desc d" and
    wf_sz_fs: "wf_size_desc_list fs" and
    wf_field_d: "wf_field_desc (component_desc d)" and
    wf_fields_d: "wf_field_descs (set (field_descs d))" and
    wf_fields_fs: "wf_field_descs (set (field_descs_list fs))" and
    y: "y = component_desc d" and
    wf_comp_d: "wf_component_descs d" and
    wf_comp_fs: "wf_component_descs_list fs" and
    i_bound:"i < size_td d + size_td_list fs" and
    lbs: "length bs = size_td d + size_td_list fs" and
    wf_desc_x: "wf_desc_tuple x" and
    wf_sz_x: "wf_size_desc_tuple x" and
    wf_decs_x: "wf_field_descs (set (field_descs_tuple x))" and
    wf_comp_x: "wf_component_descs_tuple x" and

    padding: "\<And>bs b . length bs = size_td d + size_td_list fs \<Longrightarrow>
          norm_tu (map_td field_norm (\<lambda>_. ()) d)
               (take (size_td d) (bs[i := b])) @
              norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs)
               (drop (size_td d) (bs[i := b])) =
              norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) bs) @
              norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs)
               (drop (size_td d) bs)"
    by (auto simp add: x)

  have padding_d: "\<forall>bs. length bs = size_td d \<longrightarrow>
     (\<forall>b. norm_tu (map_td field_norm (\<lambda>_. ()) d) (bs[i := b]) =
          norm_tu (map_td field_norm (\<lambda>_. ()) d) bs)"
  proof (safe)
    fix bs::"byte list" and b::"byte"
    assume lbs: "length bs = size_td d"
    from lbs obtain xbs sfx where xbs: "xbs = bs @ sfx" and lxbs: "length xbs = size_td d + size_td_list fs"
      by (metis Ex_list_of_length length_append)

    from lbs
    have eq1: "(take (size_td d) ((bs @ sfx)[i := b])) = bs[i := b]" by (simp add: list_update_append)

    from lbs
    have lbs': "length (bs[i:=b]) = size_td d" by simp

    from wf_fd_norm_tu(1)[rule_format, OF wf_fd_d lbs ] lbs
    have lnorm1:"length (norm_tu (map_td field_norm (\<lambda>_. ()) d) bs) = size_td d"
      by (simp add: export_uinfo_def length_fa_ti wf_fd_d)

    from wf_fd_norm_tu(1)[rule_format, OF wf_fd_d lbs' ] lbs'
    have lnorm2: "length (norm_tu (map_td field_norm (\<lambda>_. ()) d) (bs[i:=b])) = size_td d"
      by (simp add: export_uinfo_def length_fa_ti wf_fd_d)

    from padding [OF lxbs, of b] xbs lbs
    show "norm_tu (map_td field_norm (\<lambda>_. ()) d) (bs[i := b]) =
       norm_tu (map_td field_norm (\<lambda>_. ()) d) bs"
      apply simp
      apply (subst (asm) list_append_eq_split_conv)
       apply (simp add: eq1 lnorm1 lnorm2)
      apply (simp add: eq1)
      done
  qed


  from lbs
  have lbs_drop: "length (drop (size_td d) bs) = size_td_list fs"
    by (simp add: x)

  from lbs
  have lbs_take: "length (take (size_td d) bs) = size_td d"
    by (simp add: x)

  have lacc: "length (access_ti d v (take (size_td d) bs)) = size_td d"
    by (metis lbs_take length_fa_ti size_td_tuple.simps wf_fd_tuple.simps wf_fd_x x)

  show ?case

  proof (cases "i < size_td d")
    case True
    from True lbs
    have take_eq: "(take (size_td d) bs)[i := b] = take (size_td d) (bs[i := b])"
      by (simp add: take_update_swap)
    note hyp = Cons_typ_desc.hyps(1) [OF wf_desc_x wf_sz_x wf_decs_x wf_comp_x, simplified x, OF wf_fd_x, simplified, OF True lbs_take padding_d]
    from hyp lbs
    show ?thesis
      by  (simp add: x True nth_append lacc take_eq)
  next
    case False
    from False i_bound have i_bound': "i - size_td d  < size_td_list fs" by simp
    have padding_fs: "\<forall>bs b.
      length bs = size_td_list fs \<longrightarrow>
      norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) (bs[i - size_td d := b]) =
      norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) bs"
    proof (safe)
      fix bs::"byte list" and b::"byte"
      assume lbs: "length bs = size_td_list fs"
      from lbs obtain xbs pfx where xbs: "xbs = pfx @ bs" and lxbs: "length xbs = size_td d + size_td_list fs"
        and lpfx: "length pfx = size_td d"
        by (metis Ex_list_of_length length_append)

      from lpfx
      have drop_eq1: "drop (size_td d) xbs = bs"
        by (simp add: xbs)
      from lpfx False have drop_eq2: "(drop (size_td d) (xbs[i := b])) = bs [i - size_td d := b]"
        by (auto simp add: xbs list_update_append)
      from lpfx False
      have take_eq1: "take (size_td d) (xbs[i := b]) = pfx"
        by (simp add: xbs list_update_append)
      from lpfx False
      have take_eq2: "take (size_td d) xbs = pfx"
        by (simp add: xbs)

      have leq1: "length (norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) (xbs[i := b]))) = size_td d"
        apply (simp add: take_eq1)
        using wf_fd_norm_tu(1)[rule_format, OF wf_fd_d lpfx ] lpfx
        by (simp add: export_uinfo_def length_fa_ti wf_fd_d)
      have leq2: "length (norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) xbs)) = size_td d"
        apply (simp add: take_eq2)
        using wf_fd_norm_tu(1)[rule_format, OF wf_fd_d lpfx ] lpfx
        by (simp add: export_uinfo_def length_fa_ti wf_fd_d)

      from padding [OF lxbs, of b, simplified drop_eq1 drop_eq2]
      show "norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) (bs[i - size_td d := b]) =
      norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) bs"
        apply -
        apply (subst (asm) list_append_eq_split_conv)
        apply (simp add: leq1 leq2)
        apply simp
        done
    qed
    from False lbs have drop_eq: "((drop (size_td d) bs)[i - size_td d := b]) =
          (drop (size_td d) (bs[i := b]))"
      by (simp add: drop_update_swap)
    from False lbs have take_eq: "take (size_td d) (bs[i := b]) = take (size_td d) bs" by simp
    note hyp = Cons_typ_desc.hyps(2) [OF wf_desc_fs wf_sz_fs wf_fields_fs wf_comp_fs wf_fd_fs i_bound' lbs_drop padding_fs]
    from hyp
    show ?thesis by (simp add: x False nth_append lacc drop_eq take_eq)
  qed
next
  case (DTuple_typ_desc d nm y)
  then show ?case by (auto simp add: export_uinfo_def)
qed

lemma is_padding_byte_update_ti_id:
  assumes wf: "wf_desc (t::'a xtyp_info)"
  and wf_sz: "wf_size_desc t"
  and wf_descs: "wf_field_descs (set (field_descs t))"
  and wf_comp: "wf_component_descs t"
  and wf_fd: "wf_fd t"
  and i_bound: "i < size_td t"
  and lbs: "length bs = size_td t"
  and is_padding: "is_padding_byte (export_uinfo t) i"
shows "update_ti t (bs[i := b]) v  = update_ti t bs v"
  using is_padding_byte_update_ti_id'(1) [OF wf wf_sz wf_descs wf_comp wf_fd i_bound lbs] is_padding
  by (simp add: is_padding_byte_def export_uinfo_def)

context xmem_type
begin
lemma xmem_type_is_padding_byte_update_ti_id:
  assumes padding: "is_padding_byte (typ_uinfo_t TYPE('a)) i"
  and i_bound: "i < size_of TYPE('a)"
  and lbs: "length bs = size_of TYPE('a)"
shows "update_ti (typ_info_t TYPE('a)) (bs[i:=b]) v = update_ti (typ_info_t TYPE('a)) bs v "
proof -
  have wf: "wf_desc (typ_info_t TYPE('a))" by simp
  have wf_sz: "wf_size_desc (typ_info_t TYPE('a))" by simp
  have wf_descs: "wf_field_descs (set (field_descs (typ_info_t TYPE('a))))"
    using local.wf_field_descs by blast
  have wf_comp: "wf_component_descs (typ_info_t TYPE('a))"
    by (simp add: local.wf_component_descs)
  have wf_fd: "wf_fd (typ_info_t TYPE('a))"
    using local.wf_desc local.wf_lf wf_fdp_fd(1) wf_lf_fdp by blast
  from is_padding_byte_update_ti_id [OF wf wf_sz wf_descs wf_comp wf_fd
      i_bound [simplified size_of_def] lbs [simplified size_of_def]
      padding [simplified typ_uinfo_t_def]]
  show ?thesis .
qed
end


lemma heap_update_fold:
"sz = size_of TYPE('a) \<Longrightarrow>
  heap_update_list a (to_bytes (v::'a:: c_type) (heap_list h sz a)) h = heap_update (Ptr a) v h"
  by (simp add:heap_update_def)

lemma heap_update_padding_fold:
"sz = size_of TYPE('a) \<Longrightarrow>
  heap_update_list a (to_bytes (v::'a:: c_type) bs) h = heap_update_padding (Ptr a) v bs h"
  by (simp add:heap_update_padding_def)


context padding_base
begin
thm is_padding_byte_def
thm is_value_byte_def
end


lemma is_value_byte_access_ti_id':
  fixes t::"'a xtyp_info"
  and st::"'a xtyp_info_struct"
  and ts::"'a xtyp_info_tuple list"
  and x::"'a xtyp_info_tuple"
shows
"\<lbrakk> wf_desc t; wf_size_desc t; wf_field_descs (set (field_descs t)); wf_component_descs t; wf_fd t;
  i < size_td t; length bs = size_td t;
   \<exists>bs b. length bs = size_td t \<and> norm_tu (map_td field_norm (\<lambda>_. ()) t) (bs[i := b]) \<noteq> norm_tu (export_uinfo t) bs\<rbrakk>
  \<Longrightarrow> access_ti t v (bs[i := b]) = access_ti t v bs"

"\<lbrakk> wf_desc_struct st; wf_size_desc_struct st; wf_field_descs (set (field_descs_struct st));
  wf_component_descs_struct st;  wf_fd_struct st; i < size_td_struct st; length bs = size_td_struct st;
   \<exists>bs b. length bs = size_td_struct st \<and> norm_tu_struct (map_td_struct field_norm (\<lambda>_. ()) st) (bs[i := b]) \<noteq> norm_tu_struct ((map_td_struct field_norm (\<lambda>_. ()) st)) bs\<rbrakk>
  \<Longrightarrow> access_ti_struct st v (bs[i := b]) = access_ti_struct st v bs"

"\<lbrakk> wf_desc_list ts; wf_size_desc_list ts; wf_field_descs (set (field_descs_list ts));
  wf_component_descs_list ts; wf_fd_list ts;  i < size_td_list ts; length bs = size_td_list ts;
   \<exists>bs b. length bs = size_td_list ts \<and> norm_tu_list (map_td_list field_norm (\<lambda>_. ()) ts) (bs[i := b]) \<noteq> norm_tu_list ((map_td_list field_norm (\<lambda>_. ()) ts)) bs\<rbrakk>
  \<Longrightarrow> access_ti_list ts v (bs[i := b]) = access_ti_list ts v bs"

"\<lbrakk> wf_desc_tuple x; wf_size_desc_tuple x; wf_field_descs (set (field_descs_tuple x));
  wf_component_descs_tuple x; wf_fd_tuple x;  i < size_td_tuple x; length bs = size_td_tuple x;
   \<exists>bs b. length bs = size_td_tuple x \<and> norm_tu_tuple (map_td_tuple field_norm (\<lambda>_. ()) x) (bs[i := b]) \<noteq> norm_tu_tuple ((map_td_tuple field_norm (\<lambda>_. ()) x)) bs\<rbrakk>
  \<Longrightarrow> access_ti_tuple x v (bs[i := b]) = access_ti_tuple x v bs"
proof (induct t and st and ts and x arbitrary:  bs i  and bs i  and bs i  and bs i )
case (TypDesc algn st nm)
then show ?case by auto
next
  case (TypScalar sz algn d)
  from TypScalar obtain
    wf_d: "wf_field_desc d" and
    field_sz: "field_sz d =sz" and
    i_bound: "i < sz" and
    lbs: "length bs = sz" and
    is_val: "\<exists>bs b. length bs = sz \<and>
         field_norm sz algn d (bs[i := b]) \<noteq> field_norm sz algn d bs"
    by simp

  interpret wf: wf_field_desc d by (rule wf_d)
  show ?case
  proof (cases "wf.is_padding_byte i")
    case True
    then show ?thesis
      using field_sz lbs wf.is_padding_byte_upd_eq
      by (metis field_norm_def length_list_update is_val)

  next
    case False
    note not_padding = this
    with wf.complement field_sz i_bound have is_value: "wf.is_value_byte i" by blast
    from is_value is_val
    show ?thesis
      apply simp
      by (metis field_sz lbs padding_base.is_value_byte_acc_eq)
  qed
next
case (TypAggregate ts)
then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto
  from Cons_typ_desc.prems obtain
    wf_desc_d: "wf_desc d" and
    wf_fd_x: "wf_fd_tuple (DTuple d nm y)" and
    wf_fd_d: "wf_fd d" and
    wf_fd_fs: "wf_fd_list fs" and
    nm_notin: "nm \<notin> dt_snd ` set fs" and
    wf_desc_fs: "wf_desc_list fs" and
    wf_sz_d: "wf_size_desc d" and
    wf_sz_fs: "wf_size_desc_list fs" and
    wf_field_d: "wf_field_desc (component_desc d)" and
    wf_fields_d: "wf_field_descs (set (field_descs d))" and
    wf_fields_fs: "wf_field_descs (set (field_descs_list fs))" and
    y: "y = component_desc d" and
    wf_comp_d: "wf_component_descs d" and
    wf_comp_fs: "wf_component_descs_list fs" and
    i_bound:"i < size_td d + size_td_list fs" and
    lbs: "length bs = size_td d + size_td_list fs" and
    wf_desc_x: "wf_desc_tuple x" and
    wf_sz_x: "wf_size_desc_tuple x" and
    wf_decs_x: "wf_field_descs (set (field_descs_tuple x))" and
    wf_comp_x: "wf_component_descs_tuple x" and

    is_value: "\<exists>bs b. length bs = size_td d + size_td_list fs \<and>
          norm_tu (map_td field_norm (\<lambda>_. ()) d)
               (take (size_td d) (bs[i := b])) @
              norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs)
               (drop (size_td d) (bs[i := b])) \<noteq>
              norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) bs) @
              norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs)
               (drop (size_td d) bs)"
    by (auto simp add: x)

  from is_value obtain xbs xb where
    lxbs: "length xbs = size_td d + size_td_list fs" and
    norm_neq: "norm_tu (map_td field_norm (\<lambda>_. ()) d)
               (take (size_td d) (xbs[i := xb])) @
              norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs)
               (drop (size_td d) (xbs[i := xb])) \<noteq>
              norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) xbs) @
              norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs)
               (drop (size_td d) xbs)"
    by blast

  from lxbs have l_take1: "length (take (size_td d) (xbs[i := xb])) = size_td d"
    by simp
  from wf_fd_norm_tu(1)[rule_format, OF wf_fd_d l_take1]
  have l_norm_upd_d: "length (norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) (xbs[i := xb]))) = size_td d"
    by (metis access_ti\<^sub>0_def export_uinfo_def fd_cons_length_p wf_fd_consD wf_fd_d)

  from lxbs have l_take2: "length (take (size_td d) (xbs)) = size_td d"
    by simp
  from wf_fd_norm_tu(1)[rule_format, OF wf_fd_d l_take2]
  have l_norm_d: "length (norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) xbs)) = size_td d"
    by (metis access_ti\<^sub>0_def export_uinfo_def fd_cons_length_p wf_fd_consD wf_fd_d)

  from lbs
  have lbs_drop: "length (drop (size_td d) bs) = size_td_list fs"
    by (simp add: x)

  from lbs
  have lbs_take: "length (take (size_td d) bs) = size_td d"
    by (simp add: x)

  have lacc: "length (access_ti d v (take (size_td d) bs)) = size_td d"
    by (metis lbs_take length_fa_ti size_td_tuple.simps wf_fd_tuple.simps wf_fd_x x)

  show ?case

  proof (cases "i < size_td d")
    case True
    from True lbs
    have take_eq: "(take (size_td d) bs)[i := b] = take (size_td d) (bs[i := b])"
      by (simp add: take_update_swap)
    from True
    have drop_eq: "drop (size_td d) (xbs[i := xb]) = drop (size_td d) xbs"
      by simp
    from lxbs True
    have take_xbs_eq: "(take (size_td d) (xbs[i := xb])) = (take (size_td d) xbs)[i := xb]"
      by (simp add: take_update_swap)
    from norm_neq
    have "norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) (xbs[i := xb]))  \<noteq>
            norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) xbs)"
      by (simp add: drop_eq)
    with take_xbs_eq
    have value_d: "\<exists>bs. length bs = size_td d \<and>
       (\<exists>b. norm_tu (map_td field_norm (\<lambda>_. ()) d) (bs[i := b]) \<noteq>
            norm_tu (map_td field_norm (\<lambda>_. ()) d) bs)"
      apply simp
      using l_take2 by blast
    note hyp = Cons_typ_desc.hyps(1) [OF wf_desc_x wf_sz_x wf_decs_x wf_comp_x, simplified x, OF wf_fd_x, simplified, OF True lbs_take value_d]
    from hyp lbs
    show ?thesis
      by  (simp add: x True nth_append lacc take_eq)
  next
    case False
    from False i_bound have i_bound': "i - size_td d  < size_td_list fs" by simp

    from False lxbs
    have take_xbs: "take (size_td d) (xbs[i := xb]) = take (size_td d) xbs" by simp

    from norm_neq
    have "norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) (drop (size_td d) (xbs[i := xb])) \<noteq>
            norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) (drop (size_td d) xbs)"
      by (simp add: take_xbs)
    then
    have value_fs: "\<exists>bs b.
      length bs = size_td_list fs \<and>
      norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) (bs[i - size_td d := b]) \<noteq>
      norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) bs"
      by (metis False drop_update_swap lbs lbs_drop length_drop lxbs not_le)

    from False lbs have drop_eq: "((drop (size_td d) bs)[i - size_td d := b]) =
          (drop (size_td d) (bs[i := b]))"
      by (simp add: drop_update_swap)
    from False lbs have take_eq: "take (size_td d) (bs[i := b]) = take (size_td d) bs" by simp
    note hyp = Cons_typ_desc.hyps(2) [OF wf_desc_fs wf_sz_fs wf_fields_fs wf_comp_fs wf_fd_fs i_bound' lbs_drop value_fs]
    from hyp
    show ?thesis by (simp add: x False nth_append lacc drop_eq take_eq)
  qed
next
  case (DTuple_typ_desc d nm y)
  then show ?case by (auto simp add: export_uinfo_def)
qed

lemma is_value_byte_access_ti_id:
  assumes wf: "wf_desc t"
  assumes wf_sz: "wf_size_desc t"
  assumes wf_descs: "wf_field_descs (set (field_descs t))"
  assumes wf_comps: "wf_component_descs t"
  assumes wf_fd: "wf_fd t"
  assumes i_bound: "i < size_td t"
  assumes lbs: "length bs = size_td t"
  assumes is_value: "is_value_byte (export_uinfo t) i"
  shows "access_ti t v (bs[i := b]) = access_ti t v bs"
  using is_value_byte_access_ti_id'(1)[OF wf wf_sz wf_descs wf_comps wf_fd i_bound lbs, where v=v and b=b ] is_value
  by (simp add: is_value_byte_def export_uinfo_def)


lemma is_value_byte_access_ti_update_ti_cancel':
  fixes t::"'a xtyp_info"
  and st::"'a xtyp_info_struct"
  and ts::"'a xtyp_info_tuple list"
  and x::"'a xtyp_info_tuple"
shows
"\<lbrakk> wf_desc t; wf_size_desc t; wf_field_descs (set (field_descs t)); wf_component_descs t; wf_fd t;
  i < size_td t; length bs = size_td t; length bs' = size_td t;
   \<exists>bs b. length bs = size_td t \<and> norm_tu (map_td field_norm (\<lambda>_. ()) t) (bs[i := b]) \<noteq> norm_tu (export_uinfo t) bs\<rbrakk>
  \<Longrightarrow> access_ti t (update_ti t bs v) bs' ! i = bs ! i"

"\<lbrakk> wf_desc_struct st; wf_size_desc_struct st; wf_field_descs (set (field_descs_struct st));
  wf_component_descs_struct st;  wf_fd_struct st; i < size_td_struct st; length bs = size_td_struct st; length bs' = size_td_struct st;
   \<exists>bs b. length bs = size_td_struct st \<and> norm_tu_struct (map_td_struct field_norm (\<lambda>_. ()) st) (bs[i := b]) \<noteq> norm_tu_struct ((map_td_struct field_norm (\<lambda>_. ()) st)) bs\<rbrakk>
  \<Longrightarrow> access_ti_struct st (update_ti_struct st bs v) bs' ! i = bs ! i"

"\<lbrakk> wf_desc_list ts; wf_size_desc_list ts; wf_field_descs (set (field_descs_list ts));
  wf_component_descs_list ts; wf_fd_list ts;  i < size_td_list ts; length bs = size_td_list ts; length bs' = size_td_list ts;
   \<exists>bs b. length bs = size_td_list ts \<and> norm_tu_list (map_td_list field_norm (\<lambda>_. ()) ts) (bs[i := b]) \<noteq> norm_tu_list ((map_td_list field_norm (\<lambda>_. ()) ts)) bs\<rbrakk>
  \<Longrightarrow> access_ti_list ts (update_ti_list ts bs v) bs' ! i = bs ! i"

"\<lbrakk> wf_desc_tuple x; wf_size_desc_tuple x; wf_field_descs (set (field_descs_tuple x));
  wf_component_descs_tuple x; wf_fd_tuple x;  i < size_td_tuple x; length bs = size_td_tuple x; length bs' = size_td_tuple x;
   \<exists>bs b. length bs = size_td_tuple x \<and> norm_tu_tuple (map_td_tuple field_norm (\<lambda>_. ()) x) (bs[i := b]) \<noteq> norm_tu_tuple ((map_td_tuple field_norm (\<lambda>_. ()) x)) bs\<rbrakk>
  \<Longrightarrow> access_ti_tuple x (update_ti_tuple x bs v) bs' ! i = bs ! i"
proof (induct t and st and ts and x arbitrary:  bs bs' i v  and bs bs' i v  and bs bs' i v  and bs bs' i v )
case (TypDesc algn st nm)
then show ?case by auto
next
  case (TypScalar sz algn d)
  from TypScalar obtain
    wf_d: "wf_field_desc d" and
    field_sz: "field_sz d =sz" and
    i_bound: "i < sz" and
    lbs: "length bs = sz" and
    lbs': "length bs' = sz" and
    is_val: "\<exists>bs b. length bs = sz \<and>
         field_norm sz algn d (bs[i := b]) \<noteq> field_norm sz algn d bs"
    by simp

  interpret wf: wf_field_desc d by (rule wf_d)
  show ?case
  proof (cases "wf.is_padding_byte i")
    case True
    then show ?thesis
      using field_sz lbs wf.is_padding_byte_upd_eq
      by (metis field_norm_def length_list_update is_val)

  next
    case False
    note not_padding = this
    with wf.complement field_sz i_bound have is_value: "wf.is_value_byte i" by blast
    from is_value is_val lbs'
    show ?thesis
      by (simp add: field_sz lbs wf.is_value_byte_acc_upd_cancel)
  qed
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto

  from Cons_typ_desc.prems obtain
    wf_desc_d: "wf_desc d" and
    wf_fd_x: "wf_fd_tuple (DTuple d nm y)" and
    wf_fd_d: "wf_fd d" and
    wf_fd_fs: "wf_fd_list fs" and
    nm_notin: "nm \<notin> dt_snd ` set fs" and
    wf_desc_fs: "wf_desc_list fs" and
    wf_sz_d: "wf_size_desc d" and
    wf_sz_fs: "wf_size_desc_list fs" and
    wf_field_d: "wf_field_desc (component_desc d)" and
    wf_fields_d: "wf_field_descs (set (field_descs d))" and
    wf_fields_fs: "wf_field_descs (set (field_descs_list fs))" and
    y: "y = component_desc d" and
    wf_comp_d: "wf_component_descs d" and
    wf_comp_fs: "wf_component_descs_list fs" and
    i_bound:"i < size_td d + size_td_list fs" and
    lbs: "length bs = size_td d + size_td_list fs" and
    lbs': "length bs' = size_td d + size_td_list fs" and
    wf_desc_x: "wf_desc_tuple x" and
    wf_sz_x: "wf_size_desc_tuple x" and
    wf_decs_x: "wf_field_descs (set (field_descs_tuple x))" and
    wf_comp_x: "wf_component_descs_tuple x" and

    is_value: "\<exists>bs b. length bs = size_td d + size_td_list fs \<and>
          norm_tu (map_td field_norm (\<lambda>_. ()) d)
               (take (size_td d) (bs[i := b])) @
              norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs)
               (drop (size_td d) (bs[i := b])) \<noteq>
              norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) bs) @
              norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs)
               (drop (size_td d) bs)" and
    commutes: "fu_commutes (update_ti_t d) (update_ti_list_t fs)"
    by (auto simp add: x)


  from is_value obtain xbs xb where
    lxbs: "length xbs = size_td d + size_td_list fs" and
    norm_neq: "norm_tu (map_td field_norm (\<lambda>_. ()) d)
               (take (size_td d) (xbs[i := xb])) @
              norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs)
               (drop (size_td d) (xbs[i := xb])) \<noteq>
              norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) xbs) @
              norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs)
               (drop (size_td d) xbs)"
    by blast

  from lxbs have l_take1: "length (take (size_td d) (xbs[i := xb])) = size_td d"
    by simp
  from wf_fd_norm_tu(1)[rule_format, OF wf_fd_d l_take1]
  have l_norm_upd_d: "length (norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) (xbs[i := xb]))) = size_td d"
    by (metis access_ti\<^sub>0_def export_uinfo_def fd_cons_length_p wf_fd_consD wf_fd_d)

  from lxbs have l_take2: "length (take (size_td d) (xbs)) = size_td d"
    by simp
  from wf_fd_norm_tu(1)[rule_format, OF wf_fd_d l_take2]
  have l_norm_d: "length (norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) xbs)) = size_td d"
    by (metis access_ti\<^sub>0_def export_uinfo_def fd_cons_length_p wf_fd_consD wf_fd_d)

  from lbs
  have lbs_drop: "length (drop (size_td d) bs) = size_td_list fs"
    by (simp add: x)

  from lbs'
  have lbs'_drop: "length (drop (size_td d) bs') = size_td_list fs"
    by (simp add: x)

  from lbs
  have lbs_take: "length (take (size_td d) bs) = size_td d"
    by (simp add: x)

  from lbs'
  have lbs'_take: "length (take (size_td d) bs') = size_td d"
    by (simp add: x)

  have lacc: "length (access_ti d v (take (size_td d) bs)) = size_td d"
    by (metis lbs_take length_fa_ti size_td_tuple.simps wf_fd_tuple.simps wf_fd_x x)

  from lbs lbs'_take
  have l_acc_upd:
      "length (access_ti d (update_ti d (take (size_td d) bs)
                   (update_ti_list fs (drop (size_td d) bs) v)) (take (size_td d) bs')) = size_td d"
    by (meson  length_fa_ti wf_fd_d)
  show ?case

  proof (cases "i < size_td d")
    case True
    from True lbs
    have take_eq: "(take (size_td d) bs)[i := b] = take (size_td d) (bs[i := b])"
      by (simp add: take_update_swap)
    from True
    have drop_eq: "drop (size_td d) (xbs[i := xb]) = drop (size_td d) xbs"
      by simp
    from lxbs True
    have take_xbs_eq: "(take (size_td d) (xbs[i := xb])) = (take (size_td d) xbs)[i := xb]"
      by (simp add: take_update_swap)
    from norm_neq
    have "norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) (xbs[i := xb]))  \<noteq>
            norm_tu (map_td field_norm (\<lambda>_. ()) d) (take (size_td d) xbs)"
      by (simp add: drop_eq)
    with take_xbs_eq
    have value_d: "\<exists>bs. length bs = size_td d \<and>
       (\<exists>b. norm_tu (map_td field_norm (\<lambda>_. ()) d) (bs[i := b]) \<noteq>
            norm_tu (map_td field_norm (\<lambda>_. ()) d) bs)"
      apply simp
      using l_take2 by blast



    note hyp = Cons_typ_desc.hyps(1) [OF wf_desc_x wf_sz_x wf_decs_x wf_comp_x, simplified x, OF wf_fd_x, simplified,
        OF True lbs_take lbs'_take value_d, where v = "(update_ti_list fs (drop (size_td d) bs) v)"]
    from  lbs lbs'
    show ?thesis
      by  (simp add: x True nth_append lacc take_eq l_acc_upd  hyp)
  next
    case False
    from False i_bound have i_bound': "i - size_td d  < size_td_list fs" by simp

    from False lxbs
    have take_xbs: "take (size_td d) (xbs[i := xb]) = take (size_td d) xbs" by simp

    from norm_neq
    have "norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) (drop (size_td d) (xbs[i := xb])) \<noteq>
            norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) (drop (size_td d) xbs)"
      by (simp add: take_xbs)
    then
    have value_fs: "\<exists>bs b.
      length bs = size_td_list fs \<and>
      norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) (bs[i - size_td d := b]) \<noteq>
      norm_tu_list (map_td_list field_norm (\<lambda>_. ()) fs) bs"
      by (metis False drop_update_swap lbs lbs_drop length_drop lxbs not_le)


    from commutes have commute:
     "(update_ti d (take (size_td d) bs)
       (update_ti_list fs (drop (size_td d) bs) v)) =
       (update_ti_list fs (drop (size_td d) bs) (update_ti d (take (size_td d) bs) v))"
      apply (simp add: update_ti_t_def update_ti_list_t_def fu_commutes_def)
      apply (erule allE [where x=v])
      apply (erule allE [where x="(take (size_td d) bs)"])
      apply (erule allE [where x="(drop (size_td d) bs)"])
      using  lbs_take lbs_drop
      apply simp
      done

    from False lbs have drop_eq: "drop (size_td d) bs ! (i - size_td d) = bs ! i"
      by (simp add: drop_update_swap)

    note hyp = Cons_typ_desc.hyps(2) [OF wf_desc_fs wf_sz_fs wf_fields_fs wf_comp_fs wf_fd_fs i_bound' lbs_drop lbs'_drop value_fs]
    from hyp
    show ?thesis
      apply (simp add: x False nth_append lacc drop_eq  l_acc_upd)
      apply (simp add: commute)
      done
  qed
next
  case (DTuple_typ_desc d nm y)
  then show ?case by (auto simp add: export_uinfo_def)
qed

lemma is_value_byte_access_ti_update_ti_cancel:
   assumes wf: "wf_desc t"
  assumes wf_sz: "wf_size_desc t"
  assumes wf_descs: "wf_field_descs (set (field_descs t))"
  assumes wf_comps: "wf_component_descs t"
  assumes wf_fd: "wf_fd t"
  assumes i_bound: "i < size_td t"
  assumes lbs: "length bs = size_td t"
  assumes lbs': "length bs'= size_td t"
  assumes is_value: "is_value_byte (export_uinfo t) i"
  shows "access_ti t (update_ti t bs v) bs' ! i = bs ! i"
  using is_value_byte_access_ti_update_ti_cancel'(1) [OF wf wf_sz wf_descs wf_comps wf_fd i_bound lbs lbs'] is_value
  by (simp add: export_uinfo_def is_value_byte_def)

lemma field_lookup_is_padding_byte_focus':
  fixes t::"('a, 'b) typ_info"
  and st::"('a, 'b) typ_info_struct"
  and ts::"('a, 'b) typ_info_tuple list"
  and x::"('a, 'b) typ_info_tuple"
shows
"\<lbrakk>field_lookup t f m = Some (s, m + n); n \<le> i; i < n + size_td s; length bs = size_td t;
  wf_desc t; wf_size_desc t\<rbrakk> \<Longrightarrow>
 norm_tu (map_td field_norm (\<lambda>_. ()) t) (bs[i := b]) = norm_tu (map_td field_norm (\<lambda>_. ()) t) bs
 \<longleftrightarrow>
 norm_tu (export_uinfo s) ((take (size_td s) (drop n bs))[i - n := b]) =
   norm_tu (export_uinfo s)  (take (size_td s) (drop n bs))"


"\<lbrakk>field_lookup_struct st f m = Some (s, m + n); n \<le> i; i < n + size_td s; length bs = size_td_struct st;
  wf_desc_struct st; wf_size_desc_struct st\<rbrakk> \<Longrightarrow>
 norm_tu_struct (map_td_struct field_norm (\<lambda>_. ()) st) (bs[i := b]) = norm_tu_struct (map_td_struct field_norm (\<lambda>_. ()) st) bs
 \<longleftrightarrow>
 norm_tu (export_uinfo s) ((take (size_td s) (drop n bs))[i - n := b]) =
   norm_tu (export_uinfo s)  (take (size_td s) (drop n bs))"

"\<lbrakk>field_lookup_list ts f m = Some (s, m + n); n \<le> i; i < n + size_td s; length bs = size_td_list ts;
  wf_desc_list ts; wf_size_desc_list ts\<rbrakk> \<Longrightarrow>
 norm_tu_list (map_td_list field_norm (\<lambda>_. ()) ts) (bs[i := b]) = norm_tu_list (map_td_list field_norm (\<lambda>_. ()) ts) bs
 \<longleftrightarrow>
 norm_tu (export_uinfo s) ((take (size_td s) (drop n bs))[i - n := b]) =
   norm_tu (export_uinfo s)  (take (size_td s) (drop n bs))"

"\<lbrakk>field_lookup_tuple x f m = Some (s, m + n); n \<le> i; i < n + size_td s; length bs = size_td_tuple x;
  wf_desc_tuple x; wf_size_desc_tuple x\<rbrakk> \<Longrightarrow>
 norm_tu_tuple (map_td_tuple field_norm (\<lambda>_. ()) x) (bs[i := b]) = norm_tu_tuple (map_td_tuple field_norm (\<lambda>_. ()) x) bs
 \<longleftrightarrow>
 norm_tu (export_uinfo s) ((take (size_td s) (drop n bs))[i - n := b]) =
   norm_tu (export_uinfo s)  (take (size_td s) (drop n bs))"
proof (induct t and st and ts and x arbitrary: f m n i s bs  and f m n i s bs and f m n i s bs and f m n i s bs)
case (TypDesc algn st nm)
  then show ?case by (auto split: if_split_asm)
next
  case (TypScalar sz algn d)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto
  from Cons_typ_desc.prems obtain
    lbs: "length bs = size_td_tuple x + size_td_list fs" and
    wf_desc_x: "wf_desc_tuple (DTuple d nm y)" and
    wf_size_desc_x: "wf_size_desc_tuple (DTuple d nm y)" and
    wf_size_desc_fs: "wf_size_desc_list fs" and
    nm_notin:  "nm \<notin> dt_snd ` set fs" and
    wf_desc_fs: "wf_desc_list fs" and
    i_lower: "n \<le> i" and
    i_upper: "i < n + size_td s"
    by (auto simp add: x)

  from lbs
  have lbs_drop: "length (drop (size_td_tuple x) bs) = size_td_list fs"
    by simp

  from lbs
  have lbs_take: "length (take (size_td_tuple x) bs) = size_td_tuple (DTuple d nm y)"
    by (simp add: x)

  from lbs_take
  have take_eq1: "((take (size_td d) bs)[i := b]) = (take (size_td d) (bs[i := b]))"
    by (simp add: take_update_swap)

  from Cons_typ_desc.prems obtain f1 fxs
    where f: "f = f1#fxs"
    by (cases f) auto

  thm Cons_typ_desc.hyps [simplified x]

  show ?case
  proof (cases "f1 = nm")
    case True
    show ?thesis
    proof (cases "field_lookup d fxs m")
      case None
      from Cons_typ_desc.prems field_lookup_list_None [OF nm_notin]
      have False
        by (simp add: True None f x)
      thus ?thesis by simp
    next
      case (Some r)
      from Cons_typ_desc.prems have r: "r = (s, m + n)"
        by (simp add: x True Some f)
      hence fl: "field_lookup_tuple (DTuple d nm y) f m = Some (s, m + n)"
        by  (simp add: f True Some r)
      from td_set_wf_size_desc(4)[OF wf_size_desc_x td_set_tuple_field_lookup_tupleD, OF fl]
      have "wf_size_desc s" .
      from wf_size_desc_gt(1)[OF this]
      have "0 < size_td s" .


      with td_set_tuple_offset_size_m [OF td_set_tuple_field_lookup_tupleD, OF fl]
      have n_le: "n < size_td d"
        by auto

      have i_in_d: "i < size_td d"
        using \<open>size_td s + (m + n - m) \<le> size_td_tuple (DTuple d nm y)\<close> i_upper by auto
      have bound: "size_td s + (m + n - m) \<le> size_td_tuple (DTuple d nm y)" by fact
      from bound

      have take_eq: "(take (size_td s) (drop n (take (size_td d) bs))) =
         (take (size_td s) (drop n bs))"
        by (simp add: take_drop)
      from  Cons_typ_desc.hyps(1)[simplified x, OF fl i_lower i_upper lbs_take  wf_desc_x wf_size_desc_x] lbs bound
      show ?thesis
        by (simp add: x True Some r take_eq  nth_append i_in_d take_eq1)
    qed
  next
    case False
    with Cons_typ_desc.prems
    have fl: "field_lookup_list fs (f1 # fxs) (m + size_td d) = Some (s, m + n)"
      by (clarsimp simp add: x f False)
    hence n_bound: "size_td d \<le> n"
      by (meson field_lookup_offset_le(3) nat_add_left_cancel_le)

    from fl
    have fl: "field_lookup_list fs (f1 # fxs) (m + size_td d) = Some (s, (m + size_td d) + (n - size_td d))"
      by (metis Nat.diff_cancel field_lookup_list_offset2 field_lookup_list_offsetD)
    from n_bound
    have take_eq: "(take (size_td s) (drop (n - size_td d + size_td d) bs)) =
            (take (size_td s) (drop n bs))"
      by simp

    have i_lower': "n - size_td d \<le> i - size_td d"
      using diff_le_mono i_lower by blast

    have i_upper': "i - size_td d < n - size_td d + size_td s"
      using i_lower i_upper by linarith

    have i_notin_d: "\<not> i < size_td d"
      by (meson i_lower leD less_le_trans n_bound)

    from i_notin_d lbs_take have take_eq: "take (size_td d) (bs[i := b]) = take (size_td d) bs"
      by simp

    from i_notin_d lbs i_upper not_le have drop_eq:
      "((drop (size_td d) bs)[i - size_td d := b]) = (drop (size_td d) (bs[i := b]))"
      by (simp add: drop_update_swap)

    from Cons_typ_desc.hyps(2) [OF fl i_lower' i_upper' lbs_drop  wf_desc_fs wf_size_desc_fs]
      False n_bound
    show ?thesis
      by (simp add: x f nth_append i_notin_d take_eq drop_eq)
  qed
next
  case (DTuple_typ_desc d nm y)
then show ?case apply (cases f) by (auto split: if_split_asm)
qed

lemma field_lookup_is_padding_byte_focus:
assumes fl: "field_lookup t f 0 = Some (s, n)"
assumes i_lower: "n \<le> i"
assumes i_upper :"i < n + size_td s"
assumes wf: "wf_desc t"
assumes wf_sz: "wf_size_desc t"
shows "is_padding_byte (export_uinfo t) i = is_padding_byte (export_uinfo s) (i - n)"
proof
  assume is_padding: "is_padding_byte (export_uinfo t) i"
  show "is_padding_byte (export_uinfo s) (i - n)"
    apply (simp add: is_padding_byte_def, safe)
  proof -
    from i_upper i_lower show "i - n < size_td s" by simp
  next
    fix bs::"byte list" and b::byte
    assume lbs: "length bs = size_td s"
    from fl have le: "n + size_td s \<le> size_td t"
      by (metis add.commute field_lookup_offset_size')
    with lbs i_lower i_upper obtain pfx sfx xbs where
      xbs: "xbs = pfx @ bs @ sfx" and
      lxbs: "length xbs = size_td t" and
      lpfx: "length pfx = n"

      by (metis Ex_list_of_length ab_semigroup_add_class.add_ac(1) le_Suc_ex length_append)

    have take_eq: "take (size_td s) (drop n xbs) = bs"
      using xbs lxbs lbs lpfx le
      by simp
    from field_lookup_is_padding_byte_focus'(1) [where m = 0, simplified, OF fl i_lower i_upper lxbs wf wf_sz, where b=b]
    is_padding lxbs
    show "norm_tu (export_uinfo s) (bs[i - n := b]) =
          norm_tu (export_uinfo s) bs"
      by (simp add: take_eq export_uinfo_def is_padding_byte_def)
  qed
next
  assume is_padding: "is_padding_byte (export_uinfo s) (i - n)"
  from fl i_upper i_lower
  have i_t: "i < size_td t"
    using field_lookup_offset_size' by fastforce
  show "is_padding_byte (export_uinfo t) i"
    apply (simp add: is_padding_byte_def, safe)
  proof -
    from i_t
    show sz: "i < size_td t" .
  next
    fix bs::"byte list" and b::byte
    assume lbs: "length bs = size_td t"
    from fl i_upper i_lower i_t
    have less: "i - n < size_td t"
      by simp

    from less lbs i_lower i_upper i_t
    have sz_s: "size_td s \<le> length (drop n bs)"
      by (metis add_le_imp_le_diff field_lookup_offset_size' fl length_drop)

    from field_lookup_is_padding_byte_focus'(1) [where m = 0, simplified, OF fl i_lower i_upper lbs wf wf_sz, where b=b]
    is_padding sz_s
    show "norm_tu (export_uinfo t) (bs[i := b]) =
          norm_tu (export_uinfo t) bs"
      by (auto simp add: is_padding_byte_def export_uinfo_def)
  qed
qed

lemma field_lookup_is_value_byte_focus:
assumes fl: "field_lookup t f 0 = Some (s, n)"
assumes i_lower: "n \<le> i"
assumes i_upper :"i < n + size_td s"
assumes wf: "wf_desc t"
assumes wf_sz: "wf_size_desc t"
shows "is_value_byte (export_uinfo t) i = is_value_byte (export_uinfo s) (i - n)"
proof -
  from fl i_upper i_lower
  have i_t: "i < size_td t"
    using field_lookup_offset_size' by fastforce
  from i_lower i_upper
  have "i - n < size_td s" by simp
  with field_lookup_is_padding_byte_focus [OF fl i_lower i_upper wf wf_sz] complement_tu_padding i_t
  show ?thesis
    by (simp add: export_uinfo_size)
qed


lemma field_lookup_eq_padding_focus:
assumes fl: "field_lookup t f 0 = Some (s, n)"
assumes lbs: "length bs = size_td t"
assumes lbs': "length bs' = size_td t"
assumes wf: "wf_desc t"
assumes wf_sz: "wf_size_desc t"
assumes eq_padding: "eq_padding (export_uinfo t) bs bs'"
shows "eq_padding (export_uinfo s) (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
proof -
  from fl lbs have bound_s: "size_td s \<le> length bs - n"
    by (metis add.commute add_diff_cancel_left' diff_le_mono field_lookup_offset_size')
  from fl lbs' have bound_s': "size_td s \<le> length bs' - n"
    by (metis add.commute add_diff_cancel_left' diff_le_mono field_lookup_offset_size')
  from bound_s lbs
  have l_take: "length (take (size_td s) (drop n bs)) = size_td s"
    by simp
  from bound_s' lbs'
  have l_take': "length (take (size_td s) (drop n bs')) = size_td s"
    by simp

  show ?thesis
    apply (simp add: eq_padding_def, safe)
  proof -
    show "size_td s \<le> length bs - n" by (rule bound_s)
  next
    show "size_td s \<le> length bs' - n" by (rule bound_s')
  next
    fix i assume is_padding: "is_padding_byte (export_uinfo s) i"
    from is_padding have i_s: "i < size_td s"
      by (simp add: is_padding_byte_def)
    have n_i: "n \<le> i + n" by simp
    from i_s have i_n_bound: "i + n < n + size_td s" by simp
    show "take (size_td s) (drop n bs) ! i =
          take (size_td s) (drop n bs') ! i"

      using l_take l_take' is_padding eq_padding lbs lbs'
        field_lookup_is_padding_byte_focus [OF fl n_i i_n_bound wf wf_sz, simplified]
      by (auto simp add: eq_padding_def add.commute is_padding_byte_def)
  qed
qed



lemma field_lookup_eq_padding_focus_eq:
assumes fl: "field_lookup t f 0 = Some (s, n)"
assumes lbs: "length bs = size_td t"
assumes lbs': "length bs' = size_td t"
assumes pfx_eq: "\<And>i. i < n \<Longrightarrow> bs ! i = bs' ! i"
assumes sfx_eq: "\<And>i. n + size_td s \<le> i \<Longrightarrow> i < size_td t \<Longrightarrow> bs ! i = bs' ! i"
assumes wf: "wf_desc t"
assumes wf_sz: "wf_size_desc t"
shows "eq_padding (export_uinfo t) bs bs' =
      eq_padding (export_uinfo s) (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
proof -
  from fl lbs have bound_s: "size_td s \<le> length bs - n"
    by (metis add.commute add_diff_cancel_left' diff_le_mono field_lookup_offset_size')
  from fl lbs' have bound_s': "size_td s \<le> length bs' - n"
    by (metis add.commute add_diff_cancel_left' diff_le_mono field_lookup_offset_size')
  from bound_s lbs
  have l_take: "length (take (size_td s) (drop n bs)) = size_td s"
    by simp
  from bound_s' lbs'
  have l_take': "length (take (size_td s) (drop n bs')) = size_td s"
    by simp

  show ?thesis
  proof
    assume eq_padding: "eq_padding (export_uinfo t) bs bs'"
    show "eq_padding (export_uinfo s) (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
      by (rule field_lookup_eq_padding_focus [OF fl lbs lbs' wf wf_sz eq_padding])
  next
    assume eq_padding: "eq_padding (export_uinfo s) (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
    show "eq_padding (export_uinfo t) bs bs'"
      apply (simp add: eq_padding_def, safe)
    proof -
      show "length bs = size_td t" by (rule lbs)
    next
      show "length bs' = size_td t" by (rule lbs')
    next
      fix i
      assume is_padding: "is_padding_byte (export_uinfo t) i"
      from is_padding have i_t: "i < size_td t"
        by (simp add: is_padding_byte_def)
      show "bs ! i = bs' ! i"
      proof (cases "i < n")
        case True
        with pfx_eq show ?thesis by simp
      next
        case False
        hence i_lower: "n \<le> i" by simp
        show ?thesis
        proof (cases "i < n + size_td s")
          case True
          from field_lookup_is_padding_byte_focus [OF fl i_lower True wf wf_sz, simplified]
            eq_padding is_padding True i_lower l_take l_take'
          show ?thesis
            by (auto simp add: eq_padding_def add.commute is_padding_byte_def)
        next
          case False
          with fl i_t have i_t: "i < size_td t" by simp
          with sfx_eq i_lower False show ?thesis by simp
        qed
      qed
    qed
  qed
qed

lemma field_lookup_eq_padding_super_update_bs:
  assumes fl: "field_lookup t f 0 = Some (s, n)"
  assumes lxbs: "length xbs = size_td t"
assumes lbs: "length bs = size_td s"
assumes lbs': "length bs' = size_td s"
assumes wf: "wf_desc t"
assumes wf_sz: "wf_size_desc t"
shows "eq_padding (export_uinfo t) (super_update_bs bs xbs n) (super_update_bs bs' xbs n) =
      eq_padding (export_uinfo s) bs bs'"
proof -
  from lbs lbs' fl
  have pfx_eq: "\<And>i. i < n \<Longrightarrow> (super_update_bs bs xbs n) ! i = (super_update_bs bs' xbs n) ! i"
    by (metis (no_types, opaque_lifting) add_leD2 assms(2) field_lookup_offset_size'
        length_take less_le_trans min_def nth_append super_update_bs_def)
  from lbs lbs' fl
  have sfx_eq: "\<And>i. n + size_td s \<le> i \<Longrightarrow> i < size_td t \<Longrightarrow> (super_update_bs bs xbs n) ! i  = (super_update_bs bs' xbs n) ! i"
  proof -
    fix i :: nat
    assume a1: "n + size_td s \<le> i"
    have "n \<le> size_td t"
      by (meson add_leD2 field_lookup_offset_size' fl)
    then show "super_update_bs bs xbs n ! i = super_update_bs bs' xbs n ! i"
      using a1 lxbs lbs lbs' by (smt (verit) Many_More.nat_min_simps(1) append.assoc
          length_append length_take not_less nth_append super_update_bs_def)
  qed
  from lxbs lbs
  have lsuper: "length (super_update_bs bs xbs n) = size_td t"
    by (metis add.commute field_lookup_offset_size' fl length_super_update_bs)
  from lxbs lbs'
  have lsuper': "length (super_update_bs bs' xbs n) = size_td t"
    by (metis add.commute field_lookup_offset_size' fl length_super_update_bs)
  from lxbs lbs lsuper
  have bs: "(take (size_td s) (drop n (super_update_bs bs xbs n))) = bs"
    by (metis (no_types, lifting) append_take_drop_id append_eq_conv_conj
        append_take_drop_id length_take super_update_bs_def)
  from lxbs lbs' lsuper'
  have bs': "(take (size_td s) (drop n (super_update_bs bs' xbs n))) = bs'"
    by (metis (no_types, lifting) append_take_drop_id append_eq_conv_conj
        append_take_drop_id length_take super_update_bs_def)
  from field_lookup_eq_padding_focus_eq [OF fl lsuper lsuper' pfx_eq sfx_eq wf wf_sz]
  show ?thesis
    by (simp add: bs bs')
qed


lemma field_lookup_eq_upto_padding_focus:
assumes fl: "field_lookup t f 0 = Some (s, n)"
assumes lbs: "length bs = size_td t"
assumes lbs': "length bs' = size_td t"
assumes wf: "wf_desc t"
assumes wf_sz: "wf_size_desc t"
assumes eq_upto_padding: "eq_upto_padding (export_uinfo t) bs bs'"
shows "eq_upto_padding (export_uinfo s) (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
proof -
  from fl lbs have bound_s: "size_td s \<le> length bs - n"
    by (metis add.commute add_diff_cancel_left' diff_le_mono field_lookup_offset_size')
  from fl lbs' have bound_s': "size_td s \<le> length bs' - n"
    by (metis add.commute add_diff_cancel_left' diff_le_mono field_lookup_offset_size')
  from bound_s lbs
  have l_take: "length (take (size_td s) (drop n bs)) = size_td s"
    by simp
  from bound_s' lbs'
  have l_take': "length (take (size_td s) (drop n bs')) = size_td s"
    by simp

  show ?thesis
    apply (simp add: eq_upto_padding_def, safe)
  proof -
    show "size_td s \<le> length bs - n" by (rule bound_s)
  next
    show "size_td s \<le> length bs' - n" by (rule bound_s')
  next
    fix i assume is_value: "is_value_byte (export_uinfo s) i"
    from is_value have i_s: "i < size_td s"
      by (simp add: is_value_byte_def)
    have n_i: "n \<le> i + n" by simp
    from i_s have i_n_bound: "i + n < n + size_td s" by simp
    show "take (size_td s) (drop n bs) ! i =
          take (size_td s) (drop n bs') ! i"

      using l_take l_take' is_value eq_upto_padding lbs lbs'
        field_lookup_is_value_byte_focus [OF fl n_i i_n_bound wf wf_sz, simplified]
      by (auto simp add: eq_upto_padding_def add.commute is_value_byte_def)
  qed
qed


lemma field_lookup_eq_upto_padding_focus_eq:
assumes fl: "field_lookup t f 0 = Some (s, n)"
assumes lbs: "length bs = size_td t"
assumes lbs': "length bs' = size_td t"
assumes pfx_eq: "\<And>i. i < n \<Longrightarrow> bs ! i = bs' ! i"
assumes sfx_eq: "\<And>i. n + size_td s \<le> i \<Longrightarrow> i < size_td t \<Longrightarrow> bs ! i = bs' ! i"
assumes wf: "wf_desc t"
assumes wf_sz: "wf_size_desc t"
shows "eq_upto_padding (export_uinfo t) bs bs' =
      eq_upto_padding (export_uinfo s) (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
proof -
  from fl lbs have bound_s: "size_td s \<le> length bs - n"
    by (metis add.commute add_diff_cancel_left' diff_le_mono field_lookup_offset_size')
  from fl lbs' have bound_s': "size_td s \<le> length bs' - n"
    by (metis add.commute add_diff_cancel_left' diff_le_mono field_lookup_offset_size')
  from bound_s lbs
  have l_take: "length (take (size_td s) (drop n bs)) = size_td s"
    by simp
  from bound_s' lbs'
  have l_take': "length (take (size_td s) (drop n bs')) = size_td s"
    by simp

  show ?thesis
  proof
    assume eq_upto_padding: "eq_upto_padding (export_uinfo t) bs bs'"
    show "eq_upto_padding (export_uinfo s) (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
      by (rule field_lookup_eq_upto_padding_focus [OF fl lbs lbs' wf wf_sz eq_upto_padding])
  next
    assume eq_upto_padding: "eq_upto_padding (export_uinfo s) (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
    show "eq_upto_padding (export_uinfo t) bs bs'"
      apply (simp add: eq_upto_padding_def, safe)
    proof -
      show "length bs = size_td t" by (rule lbs)
    next
      show "length bs' = size_td t" by (rule lbs')
    next
      fix i
      assume is_value: "is_value_byte (export_uinfo t) i"
      from is_value have i_t: "i < size_td t"
        by (simp add: is_value_byte_def)
      show "bs ! i = bs' ! i"
      proof (cases "i < n")
        case True
        with pfx_eq show ?thesis by simp
      next
        case False
        hence i_lower: "n \<le> i" by simp
        show ?thesis
        proof (cases "i < n + size_td s")
          case True
          from field_lookup_is_value_byte_focus [OF fl i_lower True wf wf_sz, simplified]
            eq_upto_padding is_value True i_lower l_take l_take'
          show ?thesis
            by (auto simp add: eq_upto_padding_def add.commute )
        next
          case False
          with fl i_t have i_t: "i < size_td t" by simp
          with sfx_eq i_lower False show ?thesis by simp
        qed
      qed
    qed
  qed
qed

lemma field_lookup_eq_upto_padding_super_update_bs:
  assumes fl: "field_lookup t f 0 = Some (s, n)"
  assumes lxbs: "length xbs = size_td t"
assumes lbs: "length bs = size_td s"
assumes lbs': "length bs' = size_td s"
assumes wf: "wf_desc t"
assumes wf_sz: "wf_size_desc t"
shows "eq_upto_padding (export_uinfo t) (super_update_bs bs xbs n) (super_update_bs bs' xbs n) =
      eq_upto_padding (export_uinfo s) bs bs'"
proof -
  from lbs lbs' fl
  have pfx_eq: "\<And>i. i < n \<Longrightarrow> (super_update_bs bs xbs n) ! i = (super_update_bs bs' xbs n) ! i"
    by (metis (no_types, opaque_lifting) add_leD2 assms(2) field_lookup_offset_size'
        length_take less_le_trans min_def nth_append super_update_bs_def)
  from lbs lbs' fl
  have sfx_eq: "\<And>i. n + size_td s \<le> i \<Longrightarrow> i < size_td t \<Longrightarrow> (super_update_bs bs xbs n) ! i  = (super_update_bs bs' xbs n) ! i"
  proof -
    fix i :: nat
    assume a1: "n + size_td s \<le> i"
    have "n \<le> size_td t"
      by (meson add_leD2 field_lookup_offset_size' fl)
    then show "super_update_bs bs xbs n ! i = super_update_bs bs' xbs n ! i"
      using a1 lxbs lbs lbs' by (smt (verit) Many_More.nat_min_simps(1) append.assoc
          length_append length_take not_less nth_append super_update_bs_def)
  qed
  from lxbs lbs
  have lsuper: "length (super_update_bs bs xbs n) = size_td t"
    by (metis add.commute field_lookup_offset_size' fl length_super_update_bs)
  from lxbs lbs'
  have lsuper': "length (super_update_bs bs' xbs n) = size_td t"
    by (metis add.commute field_lookup_offset_size' fl length_super_update_bs)
  from lxbs lbs lsuper
  have bs: "(take (size_td s) (drop n (super_update_bs bs xbs n))) = bs"
    by (metis (no_types, lifting) append_take_drop_id append_eq_conv_conj
        append_take_drop_id length_take super_update_bs_def)
  from lxbs lbs' lsuper'
  have bs': "(take (size_td s) (drop n (super_update_bs bs' xbs n))) = bs'"
    by (metis (no_types, lifting) append_take_drop_id append_eq_conv_conj
        append_take_drop_id length_take super_update_bs_def)
  from field_lookup_eq_upto_padding_focus_eq [OF fl lsuper lsuper' pfx_eq sfx_eq wf wf_sz]
  show ?thesis
    by (simp add: bs bs')
qed

lemma field_lookup_wf_size_desc_pres:
  fixes t::"('a, 'b) typ_desc"
  and st::"('a, 'b) typ_struct"
  and ts::"('a, 'b) typ_tuple list"
  and x::"('a, 'b) typ_tuple"
shows
"wf_size_desc t \<Longrightarrow> field_lookup t f n = Some (s, m) \<Longrightarrow> wf_size_desc s"
"wf_size_desc_struct st \<Longrightarrow> field_lookup_struct st f n = Some (s, m) \<Longrightarrow> wf_size_desc s"
"wf_size_desc_list ts \<Longrightarrow> field_lookup_list ts f n = Some (s, m) \<Longrightarrow> wf_size_desc s"
"wf_size_desc_tuple x \<Longrightarrow> field_lookup_tuple x f n = Some (s, m) \<Longrightarrow> wf_size_desc s"
by (induct t and st and ts and x arbitrary: n s m f and n s m f  and n s m f and n s m f)
   (auto split: if_split_asm option.splits)


lemma field_lookup_update_ti_super_update_bs_conv:
  fixes t::"('a,'b) typ_info"
  and st::"('a,'b) typ_info_struct"
  and ts::"('a,'b) typ_info_tuple list"
  and x::"('a,'b) typ_info_tuple"
shows
"\<lbrakk>field_lookup t f m = Some (s, m + n);  length bs = size_td s; length xbs = size_td t;
  wf_fd t; wf_desc t; wf_size_desc t\<rbrakk> \<Longrightarrow>
 update_ti s bs v =
    update_ti t (super_update_bs bs (access_ti t v xbs) n) v"

"\<lbrakk>field_lookup_struct st f m = Some (s, m + n);  length bs = size_td s; length xbs = size_td_struct st;
  wf_fd_struct st; wf_desc_struct st; wf_size_desc_struct st\<rbrakk> \<Longrightarrow>
 update_ti s bs v =
    update_ti_struct st (super_update_bs bs (access_ti_struct st v xbs) n) v"

"\<lbrakk>field_lookup_list ts f m = Some (s, m + n);  length bs = size_td s; length xbs = size_td_list ts;
  wf_fd_list ts; wf_desc_list ts; wf_size_desc_list ts\<rbrakk> \<Longrightarrow>
 update_ti s bs v =
    update_ti_list ts (super_update_bs bs (access_ti_list ts v xbs) n) v"

"\<lbrakk>field_lookup_tuple x f m = Some (s, m + n);  length bs = size_td s; length xbs = size_td_tuple x;
  wf_fd_tuple x; wf_desc_tuple x; wf_size_desc_tuple x\<rbrakk> \<Longrightarrow>
 update_ti s bs v =
    update_ti_tuple x (super_update_bs bs (access_ti_tuple x v xbs) n) v"
proof (induct t and st and ts and x arbitrary: f m n xbs v and f m n xbs v and f m n xbs v and f m n xbs v)
case (TypDesc algn st nm)
  then show ?case
    by (auto split: if_split_asm)
      (metis TypDesc.prems(3) TypDesc.prems(4) access_ti.simps length_fa_ti super_update_bs_same_length)
next
  case (TypScalar  algn st d)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto
  from Cons_typ_desc.prems obtain
    lxbs: "length xbs = size_td_tuple x + size_td_list fs" and
    lbs: "length bs = size_td s" and
    wf_fd_x: "wf_fd_tuple (DTuple d nm y)" and
    wf_desc_x: "wf_desc_tuple (DTuple d nm y)" and
    wf_fd_fs: "wf_fd_list fs" and
    wf_size_desc_x: "wf_size_desc_tuple (DTuple d nm y)" and
    wf_size_desc_fs: "wf_size_desc_list fs" and
    nm_notin:  "nm \<notin> dt_snd ` set fs" and
    wf_desc_fs: "wf_desc_list fs" and
    commutes: "fu_commutes (update_ti_t d) (update_ti_list_t fs)"
    by (auto simp add: x)

  from  wf_fd_cons_listD [OF wf_fd_fs ]
  have fd_cons_fs: "fd_cons_list fs" .

  from wf_fd_x have fd_cons_d: "fd_cons d" by (simp add: x wf_fd_consD)

  from lxbs
  have lxbs_drop: "length (drop (size_td_tuple x) xbs) = size_td_list fs"
    by simp

  from lxbs
  have lxbs_take: "length (take (size_td_tuple x) xbs) = size_td_tuple (DTuple d nm y)"
    by (simp add: x)

  from lxbs
  have ldrop_xbs: "length  (drop (size_td d) xbs) = size_td_list fs"
    by (simp add: x)

  from lxbs wf_fd_x
  have eq1: "length (access_ti d v (take (size_td d) xbs)) = size_td d"
    by (metis lxbs_take length_fa_ti size_td_tuple.simps wf_fd_tuple.simps x)

  from Cons_typ_desc.prems obtain f1 fxs
    where f: "f = f1#fxs"
    by (cases f) auto


  show ?case
  proof (cases "f1 = nm")
    case True
    show ?thesis
    proof (cases "field_lookup d fxs m")
      case None
      from Cons_typ_desc.prems field_lookup_list_None [OF nm_notin]
      have False
        by (simp add: True None f x)
      thus ?thesis by simp
    next
      case (Some r)
      from Cons_typ_desc.prems have r: "r = (s, m + n)"
        by (simp add: x True Some f)
      hence fl: "field_lookup_tuple (DTuple d nm y) f m = Some (s, m + n)"
        by  (simp add: f True Some r)

      from td_set_wf_size_desc(4)[OF wf_size_desc_x td_set_tuple_field_lookup_tupleD, OF fl]
      have "wf_size_desc s" .
      from wf_size_desc_gt(1)[OF this]
      have "0 < size_td s" .


      with td_set_tuple_offset_size_m [OF td_set_tuple_field_lookup_tupleD, OF fl]
      have n_le: "n < size_td d"
        by auto


      have bound: "size_td s + (m + n - m) \<le> size_td_tuple (DTuple d nm y)" by fact
      have bound1: "n + length bs \<le> size_td d"
        by (metis add.commute bound diff_add_inverse lbs size_td_tuple.simps)

      from fd_cons_fs  ldrop_xbs
      have upd_id: "(update_ti_list fs (access_ti_list fs v (drop (size_td d) xbs)) v) = v"
        apply (clarsimp simp add: fd_cons_list_def fd_cons_desc_def update_ti_list_t_def)
        apply (simp add: fd_cons_update_access_def fd_cons_length_def)
        done

      note hyp = Cons_typ_desc.hyps(1)[simplified x, OF fl lbs lxbs_take wf_fd_x wf_desc_x wf_size_desc_x, where v =v]
      show ?thesis apply (simp add: x True r hyp)
        by (simp add: super_update_bs_append_drop_first eq1 bound1 super_update_bs_append_take_first upd_id)
    qed
  next
    case False
    with Cons_typ_desc.prems
    have fl1: "field_lookup_list fs (f1 # fxs) (m + size_td d) = Some (s, m + n)"
      by (clarsimp simp add: x f False)
    hence n_bound: "size_td d \<le> n"
      by (meson field_lookup_offset_le(3) nat_add_left_cancel_le)

    from fl1
    have fl: "field_lookup_list fs (f1 # fxs) (m + size_td d) = Some (s, (m + size_td d) + (n - size_td d))"
      by (metis Nat.diff_cancel field_lookup_list_offset2 field_lookup_list_offsetD)
    from n_bound
    have take_eq: "(take (size_td s) (drop (n - size_td d + size_td d) xbs)) =
            (take (size_td s) (drop n xbs))"
      by simp

    from fd_cons_d lxbs_take eq1
    have upd_d_id: "update_ti d (access_ti d v (take (size_td d) xbs)) v = v"
     apply  (clarsimp simp add: fd_cons_def fd_cons_desc_def update_ti_t_def)
      apply (simp add: fd_cons_update_access_def x)
      apply (erule allE [where x= "v"])
      apply (erule allE [where x= "(take (size_td d) xbs)"])
      apply (simp add: eq1)
      done

    from ldrop_xbs fd_cons_fs
    have lacc_fs: "length (access_ti_list fs v (drop (size_td d) xbs)) = size_td_list fs"
      by (simp add: fd_cons_list_def fd_cons_desc_def fd_cons_length_def)

    from td_set_field_lookup_rev''(3) [rule_format] fl
    have "(s, (m + size_td d) + (n - size_td d)) \<in> td_set_list fs (m + size_td d)"
      by blast
    from td_set_offset_size''(3)[rule_format, OF this, simplified]
    have bound: "size_td s + (n - size_td d) \<le> size_td_list fs".

    from lacc_fs n_bound bound lbs
    have lsuper: "length (super_update_bs bs (access_ti_list fs v (drop (size_td d) xbs)) (n - size_td d)) = size_td_list fs"
      by (simp add: super_update_bs_length)


    from commutes have
     commute: "update_ti d (access_ti d v (take (size_td d) xbs))
        (update_ti_list fs (super_update_bs bs (access_ti_list fs v (drop (size_td d) xbs)) (n - size_td d)) v) =
     update_ti_list fs (super_update_bs bs (access_ti_list fs v (drop (size_td d) xbs)) (n - size_td d))
        (update_ti d (access_ti d v (take (size_td d) xbs)) v)"
      apply (simp add: fu_commutes_def)
      apply (erule allE [where x = "v"])
      apply (erule allE [where x = "access_ti d v (take (size_td d) xbs)"])
      apply (erule allE [where x = "super_update_bs bs (access_ti_list fs v (drop (size_td d) xbs)) (n - size_td d)"])
      apply (simp add: update_ti_list_t_def update_ti_t_def eq1 lsuper)
      done


    note hyp = Cons_typ_desc.hyps(2)[simplified x, OF fl lbs lxbs_drop wf_fd_fs wf_desc_fs wf_size_desc_fs, simplified x, simplified]
    show ?thesis
      apply (simp add: x f eq1 )
      apply (simp add: super_update_bs_append_drop_second eq1 n_bound super_update_bs_append_take_second)
      apply (simp add: commute)
      apply (simp add: hyp)
      apply (simp add: upd_d_id)
      done
  qed
next
  case (DTuple_typ_desc d nm y)
  then show ?case by (auto split: if_split_asm)
qed

lemma access_ti_super_update_bs_of_wf:
  fixes t::"('a, 'b) typ_info"
  and st::"('a, 'b) typ_info_struct"
  and ts::"('a, 'b) typ_info_tuple list"
  and x::"('a, 'b) typ_info_tuple"
shows
"\<lbrakk>field_lookup t f m = Some (s, m + n); length bs' = size_td s; length bs = size_td t;
  wf_fd t; wf_desc t; wf_size_desc t\<rbrakk> \<Longrightarrow>
   access_ti t (update_ti s (access_ti\<^sub>0 s w) v) (super_update_bs bs' bs n) =
    super_update_bs (access_ti s w bs') (access_ti t v bs) n"

"\<lbrakk>field_lookup_struct st f m = Some (s, m + n); length bs' = size_td s; length bs = size_td_struct st;
  wf_fd_struct st; wf_desc_struct st; wf_size_desc_struct st\<rbrakk> \<Longrightarrow>
   access_ti_struct st (update_ti s (access_ti\<^sub>0 s w) v) (super_update_bs bs' bs n) =
     super_update_bs (access_ti s w bs')  (access_ti_struct st v bs) n"

"\<lbrakk>field_lookup_list ts f m = Some (s, m + n); length bs' = size_td s; length bs = size_td_list ts;
  wf_fd_list ts; wf_desc_list ts; wf_size_desc_list ts\<rbrakk> \<Longrightarrow>
   access_ti_list ts (update_ti s (access_ti\<^sub>0 s w) v) (super_update_bs bs' bs n) =
     super_update_bs (access_ti s w bs') (access_ti_list ts v bs) n"

"\<lbrakk>field_lookup_tuple x f m = Some (s, m + n); length bs' = size_td s; length bs = size_td_tuple x;
  wf_fd_tuple x; wf_desc_tuple x; wf_size_desc_tuple x\<rbrakk> \<Longrightarrow>
   access_ti_tuple x (update_ti s (access_ti\<^sub>0 s w) v) (super_update_bs bs' bs n) =
     super_update_bs (access_ti s w bs')  (access_ti_tuple x v bs) n"
proof (induct t and st and ts and x arbitrary: f m n bs and f m n bs and f m n bs and f m n bs)
  case (TypDesc algn st nm)
  note fd = wf_fd_field_lookupD[OF TypDesc(2, 5), THEN wf_fd_consD]
  have "length bs = size_td s \<Longrightarrow>
    access_ti s (update_ti s (access_ti\<^sub>0 s w) v) bs = access_ti s w bs" for bs
    using fd
    unfolding fd_cons_def fd_cons_desc_def fd_cons_access_update_def fd_cons_update_access_def
    by simp (metis access_ti\<^sub>0 fd fd_cons_length_p length_replicate update_ti_update_ti_t)
  then show ?case
    using TypDesc(2-) length_fa_ti[OF \<open>wf_fd (TypDesc algn st nm)\<close>]
    by (auto split: if_splits
             simp: super_update_bs_same_length TypDesc(1))
next
  case (TypScalar sz algn d)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto
  from Cons_typ_desc.prems have
    lbs: "length bs = size_td_tuple x + size_td_list fs" and
    wf_fd_x: "wf_fd_tuple (DTuple d nm y)" and
    wf_desc_x: "wf_desc_tuple (DTuple d nm y)" and
    wf_fd_fs: "wf_fd_list fs" and
    wf_size_desc_x: "wf_size_desc_tuple (DTuple d nm y)" and
    wf_size_desc_fs: "wf_size_desc_list fs" and
    nm_notin:  "nm \<notin> dt_snd ` set fs" and
    wf_desc_fs: "wf_desc_list fs" and
    bs': "length bs' = size_td s"
    by (auto simp add: x)

  { fix bs bs' :: "byte list" and v
    assume bs: "length bs = size_td d" and bs': "length bs' = size_td_list fs"
    with \<open>wf_fd_list (x # fs)\<close> have x_fs:
      "access_ti_list fs (update_ti_tuple_t x bs v) bs' = access_ti_list fs v bs'"
      by (simp add: fa_fu_ind_def x)
    then have "access_ti_list fs (update_ti d bs v) bs' = access_ti_list fs v bs'"
      by (simp add: update_ti_tuple_t_def bs x) }
  note fs_x = this

  from lbs
  have lbs_drop: "length (drop (size_td_tuple x) bs) = size_td_list fs"
    by simp

  from lbs
  have lbs_take: "length (take (size_td_tuple x) bs) = size_td_tuple (DTuple d nm y)"
    by (simp add: x)

  from lbs wf_fd_x
  have eq1: "length (access_ti d v (take (size_td d) bs)) = size_td d"
    by (metis lbs_take length_fa_ti size_td_tuple.simps wf_fd_tuple.simps x)

  from Cons_typ_desc.prems obtain f1 fxs
    where f: "f = f1#fxs"
    by (cases f) auto

  have wf_s: "wf_fd s"
    using Cons_typ_desc.prems(1) Cons_typ_desc.prems(4) wf_fd_field_lookup(3) by blast


  let ?v = "update_ti s (access_ti\<^sub>0 s w) v"

  have len_acc_w[simp]: "length (access_ti\<^sub>0 s w) = size_td s"
    using length_fa_ti[OF wf_s] by (simp add: access_ti\<^sub>0_def)

  show ?case
  proof (cases "f1 = nm")
    case True
    show ?thesis
    proof (cases "field_lookup d fxs m")
      case None
      from Cons_typ_desc.prems field_lookup_list_None [OF nm_notin]
      have False
        by (simp add: True None f x)
      thus ?thesis by simp
    next
      case (Some r)
      from Cons_typ_desc.prems have r: "r = (s, m + n)"
        by (simp add: x True Some f)
      hence fl: "field_lookup_tuple (DTuple d nm y) f m = Some (s, m + n)"
        by  (simp add: f True Some r)
      from td_set_wf_size_desc(4)[OF wf_size_desc_x td_set_tuple_field_lookup_tupleD, OF fl]
      have "wf_size_desc s" .
      from wf_size_desc_gt(1)[OF this]
      have "0 < size_td s" .

      with td_set_tuple_offset_size_m [OF td_set_tuple_field_lookup_tupleD, OF fl]
      have n_le: "n < size_td d"
        by auto

      have bound: "size_td s + (m + n - m) \<le> size_td_tuple (DTuple d nm y)" by fact
      from bound
      have take_eq: "(take (size_td s) (drop n (take (size_td d) bs))) =
         (take (size_td s) (drop n bs))"
        by (simp add: take_drop)

      have take_eq1: "take (size_td s) (drop n (take (size_td d) bs)) = take (size_td s) (drop n bs)"
        using take_eq by blast

      have l_take_s: "length (take (size_td s) (drop n bs)) = size_td s"
        using bound lbs_take by auto

      have sz_s: "size_td s \<le> length bs - n"
        using l_take_s by auto

      from fl
      have fd_cons_s: "fd_cons s"
        using wf_fd_consD wf_fd_field_lookup(4) wf_fd_x by blast

      have sz: "size_td s + n \<le> size_td d" "length bs = size_td d + size_td_list fs"
        using lbs x bound by auto
      with bs' have super_update_bs_simps[simp]:
        "take (size_td d) (super_update_bs bs' bs n) =
          super_update_bs bs' (take (size_td d) bs) n"
        "drop (size_td d) (super_update_bs bs' bs n) = drop (size_td d) bs"
        by (auto simp: super_update_bs_def take_drop)

      have hyp:
        "access_ti d (update_ti s (access_ti\<^sub>0 s w) v)
            (super_update_bs bs' (take (size_td d) bs) n) =
          super_update_bs (access_ti s w bs') (access_ti d v (take (size_td d) bs)) n"
        using Cons_typ_desc.hyps(1) fl lbs_take wf_fd_x wf_desc_x wf_size_desc_x bs'
        by (auto simp: x)

      have length_take_bs: "length (take (size_td d) bs) = size_td d"
        using sz by auto

      have fl_d_s: "field_lookup d fxs m = Some (s, m + n)"
        using fl by (simp add: True f)

      have wf_d: "wf_fd d" "wf_desc d" "wf_size_desc d"
        using wf_fd_x wf_desc_x wf_size_desc_x by auto
      note length_fa_ti[OF wf_d(1), simp]

      show ?thesis using lbs bound fd_cons_length[OF \<open>fd_cons s\<close> bs']
        apply (simp add: x True Some r eq1 hyp bs' super_update_bs_append1)
        apply (subst field_lookup_update_ti_super_update_bs_conv(1)[OF fl_d_s len_acc_w length_take_bs wf_d])
        apply (subst fs_x)
        apply simp_all
        done
    qed
  next
    case False
    with Cons_typ_desc.prems
    have fl: "field_lookup_list fs (f1 # fxs) (m + size_td d) = Some (s, m + n)"
      by (clarsimp simp add: x f False)
    hence n_bound: "size_td d \<le> n"
      by (meson field_lookup_offset_le(3) nat_add_left_cancel_le)

    have fl: "field_lookup_list fs (f1 # fxs) (m + size_td d) =
        Some (s, (m + size_td d) + (n - size_td d))"
      by (metis Nat.diff_cancel field_lookup_list_offset2 field_lookup_list_offsetD fl)

    have hyp:
      "access_ti_list fs (update_ti s (access_ti\<^sub>0 s w) v)
        (super_update_bs bs' (drop (size_td d) bs) (n - size_td d)) =
      super_update_bs (access_ti s w bs')
        (access_ti_list fs v (drop (size_td d) bs)) (n - size_td d)"
      using Cons_typ_desc.hyps(2) fl bs' lbs_drop wf_fd_fs wf_desc_fs wf_size_desc_fs
      by (simp add: x)

    have super_update_bs_simps[simp]:
      "take (size_td d) (super_update_bs bs' bs n) = take (size_td d) bs"
      "drop (size_td d) (super_update_bs bs' bs n) =
        super_update_bs bs' (drop (size_td d) bs) (n - size_td d)"
      using n_bound lbs x by (simp_all add: super_update_bs_def drop_take)

    have fl_x: "field_lookup_list (x # fs) [nm] 0 = Some (d, 0)"
      by (simp add: x)
    have disj: "disj_fn [nm] f"
      using False f by (auto simp: disj_fn_def)

    from fa_fu_lookup_disj(3)[rule_format, OF fl_x Cons_typ_desc(3) disj \<open>wf_fd_list (x # fs)\<close>]
    have acc_upd: "length bs = size_td s \<Longrightarrow> length bs' = size_td d \<Longrightarrow>
      access_ti d (update_ti s bs v) bs' = access_ti d v bs'" for bs bs' v
      by (simp add: fa_fu_ind_def update_ti_t_def)

    from False n_bound lbs
    show ?thesis
      by (simp add: x f hyp eq1 nth_append super_update_bs_append2 acc_upd)
  qed
next
  case (DTuple_typ_desc d nm y)
  then show ?case apply (cases f) by (auto split: if_split_asm)
qed

lemma heap_update_list_same:
  assumes p_no_overflow: "unat p + length bs \<le> addr_card"
  assumes same_pfx: "\<And>i. i < length bs \<Longrightarrow> bs ! i = hp (p + word_of_nat i)"
  shows  "heap_update_list p bs hp = hp"
  using p_no_overflow same_pfx
proof (induct bs arbitrary: p hp)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  from Cons.prems obtain
    no_overflow: "Suc (unat p + length bs) \<le> addr_card" and
    same: "(\<And>i. i < Suc (length bs) \<Longrightarrow> (b # bs) ! i = hp (p + word_of_nat i)) "
    by clarsimp

  from no_overflow have no_overflow': "unat (p + 1) + length bs \<le> addr_card"
   by (metis (no_types, opaque_lifting) Suc_leD
        add.commute add_Suc_right add_leD1 comm_monoid_add_class.add_0 unatSuc unat_0)

  {
    fix i
    assume bound: "i < length bs"
    from same [where i="Suc i", simplified, OF bound]
    have "bs ! i = hp (p + (1 + word_of_nat i))" .
    then
    have "bs ! i = hp (p + 1 + word_of_nat i)"
      by (metis group_cancel.add1)
  } note same' = this


  from same [where i=0] have hp_eq: "hp(p := b) = hp" by simp
  note hyp = Cons.hyps [where p="p+1", OF no_overflow' same']
  then show ?case by (simp add: hp_eq)
qed

lemma heap_update_list_same_prefix:
  assumes p_no_overflow: "unat p + length pfx + length bs \<le> addr_card"
  assumes same_pfx: "\<And>i. i < length pfx \<Longrightarrow> pfx ! i = hp (p + word_of_nat i)"
  shows  "heap_update_list p (pfx @ bs) hp = heap_update_list (p + word_of_nat (length pfx)) bs hp"
  using p_no_overflow same_pfx
proof (induct pfx arbitrary: p bs hp)
  case Nil
  then show ?case by simp
next
  case (Cons x pfx)
  from Cons.prems obtain
    no_overflow: "Suc (unat p + length pfx + length bs) \<le> addr_card" and
    same: "(\<And>i. i < Suc (length pfx) \<Longrightarrow> (x # pfx) ! i = hp (p + word_of_nat i))"
    by clarsimp


  from no_overflow have no_overflow': "unat (p + 1) + length pfx + length bs \<le> addr_card"
    by (metis (no_types, opaque_lifting) Suc_leD ab_semigroup_add_class.add_ac(1)
        add.commute add_Suc_right add_leD1 comm_monoid_add_class.add_0 unatSuc unat_0)

  {
    fix i
    assume bound: "i < length pfx"
    from same [where i="Suc i", simplified, OF bound]
    have "pfx ! i = hp (p + (1 + word_of_nat i))" .
    then
    have "pfx ! i = hp (p + 1 + word_of_nat i)"
      by (metis group_cancel.add1)
  } note same' = this

  have add_eq: "p + 1 + word_of_nat (length pfx) = p + (1 + word_of_nat (length pfx))"
    using add.assoc by blast
  from same [where i=0] have hp_eq: "hp(p := x) = hp" by simp
  note hyp =  Cons.hyps [where p="p+1", OF no_overflow' same']
  then show ?case by (simp add: hp_eq add_eq)
qed

lemma heap_update_list_same_suffix:
  assumes p_no_overflow: "unat p + length sfx + length bs  \<le> addr_card"
  assumes same_sfx: "\<And>i. i < length sfx \<Longrightarrow> sfx ! i = hp (p + word_of_nat (length bs + i))"
  shows  "heap_update_list p (bs @ sfx) hp = heap_update_list p bs hp"
  using p_no_overflow same_sfx
proof (induct bs arbitrary: p sfx hp)
  case Nil
  then show ?case by (simp add: heap_update_list_same)
next
  case (Cons b bs)
  from Cons.prems obtain no_overflow: "Suc (unat p + length sfx + length bs) \<le> addr_card" and
    same : "\<And>i. i < length sfx \<Longrightarrow> sfx ! i = hp (p + word_of_nat (Suc (length bs) + i))"
    by clarsimp

  from no_overflow have no_overflow': "unat (p + 1) + length sfx + length bs \<le> addr_card"
    by (metis (no_types, opaque_lifting) Suc_leD ab_semigroup_add_class.add_ac(1)
        add.commute add_Suc_right add_leD1 comm_monoid_add_class.add_0 unatSuc unat_0)

  {
    fix i
    assume i_bound: "i < length sfx"
    from same [OF i_bound] have prem: "sfx ! i = hp (p + word_of_nat (Suc (length bs) + i))" .
    from i_bound no_overflow
    have "Suc (i + length bs) < addr_card"
      by simp
    then
    have neq: "p \<noteq> p + 1 + word_of_nat (length bs + i)"
      by (metis (no_types, opaque_lifting) ab_semigroup_add_class.add_ac(1) add.commute add_cancel_right_right
          len_of_addr_card not_gr_zero of_nat_Suc unat_of_nat_eq unsigned_0 zero_less_Suc)

    from neq [symmetric]
    have hp_eq: "(hp(p := b)) (p + 1 + word_of_nat (length bs + i)) = hp (p + 1 + word_of_nat (length bs + i))"
      by (rule fun_upd_other)
    have add_eq: "(p + 1 + word_of_nat (length bs + i)) = (p + word_of_nat (Suc (length bs) + i))"
      by simp

    have "sfx ! i = (hp(p := b)) (p + 1 + word_of_nat (length bs + i))"
      apply (subst hp_eq)
      apply (subst prem )
      apply (simp only: add_eq)
      done
  } note same' = this
  note hyp = Cons.hyps [OF no_overflow', where hp="(hp(p := b))", OF same' ]
  show ?case apply (simp add: hyp) by (simp add: fun_upd_def)
qed


lemma heap_update_list_same_prefix_suffix:
  assumes p_no_overflow: "unat p + length pfx + length bs + length sfx \<le> addr_card"
  assumes same_pfx: "\<And>i. i < length pfx \<Longrightarrow> pfx ! i = hp (p + word_of_nat i)"
  assumes same_sfx: "\<And>i. i < length sfx \<Longrightarrow> sfx ! i = hp (p + word_of_nat (length pfx + length bs + i))"
  shows  "heap_update_list p (pfx @ bs @ sfx) hp = heap_update_list (p + word_of_nat (length pfx)) bs hp"
proof -
  from p_no_overflow
  have no_overflow_pfx: "unat p + length pfx + length (bs @ sfx) \<le> addr_card" by simp

  from heap_update_list_same_prefix [where pfx=pfx and bs="bs@sfx", OF no_overflow_pfx same_pfx]

  have "heap_update_list p (pfx @ bs @ sfx) hp =
          heap_update_list (p + word_of_nat (length pfx)) (bs @ sfx) hp" .
  also

  from p_no_overflow have "unat p + length pfx \<le> addr_card"
    by simp
  then
  have "unat (p + word_of_nat (length pfx)) \<le> unat p + length pfx"
    by (simp add: unat_le_helper)

  with p_no_overflow
  have no_overflow_sfx: "unat (p + word_of_nat (length pfx)) + length sfx + length bs   \<le> addr_card"
    by simp

  from same_sfx p_no_overflow have same_sfx': "\<And>i. i < length sfx \<Longrightarrow>
      sfx ! i = hp (p + word_of_nat (length pfx) + word_of_nat (length bs + i))"
    apply simp
    by (simp add: ab_semigroup_add_class.add_ac(1))
  from heap_update_list_same_suffix [where p="p + word_of_nat (length pfx)" and bs=bs and sfx =sfx and hp=hp,
     OF no_overflow_sfx same_sfx']
  have "heap_update_list (p + word_of_nat (length pfx)) (bs @ sfx) hp =
          heap_update_list (p + word_of_nat (length pfx)) bs hp"  .
  finally show ?thesis .
qed

lemma heap_update_list_super_update_bs_heap_list:
  assumes p_no_overflow: "unat p + m \<le> addr_card"
  assumes n_m: "n + length bs \<le> m"
  shows  "heap_update_list (p + word_of_nat n) bs hp = heap_update_list p (super_update_bs bs (heap_list hp m p) n) hp"
proof -
  have heap_list_hp: "\<And>i. i < m \<Longrightarrow> (heap_list hp m p) ! i = hp (p + word_of_nat i)"
    by (rule heap_list_nth)

  obtain pfx sfx where
    super: "super_update_bs bs (heap_list hp m p) n = pfx @ bs @ sfx"  and
    pfx: "pfx = take n (heap_list hp m p)" and
    sfx: "sfx = drop (n + length bs) (heap_list hp m p)" and
    lpfx: "length pfx = n" and
    lsfx: "length sfx = m - n - length bs"
    using n_m
    by (simp add: super_update_bs_def )

  have bounds: "unat p + length pfx + length bs + length sfx \<le> addr_card"
    using lpfx p_no_overflow n_m lsfx
    by simp

  have same_pfx: "\<And>i. i < length pfx \<Longrightarrow> pfx ! i = hp (p + word_of_nat i)"
    using heap_list_hp
    by (simp add: pfx)

  have same_sfx: "\<And>i. i < length sfx \<Longrightarrow> sfx ! i = hp (p + word_of_nat (length pfx + length bs + i))"
    using heap_list_hp
    by (simp add: sfx lpfx)
  from heap_update_list_same_prefix_suffix [OF bounds same_pfx same_sfx]
  show ?thesis
    by (simp add: super lpfx)
qed


lemma append_take_dropI: "xs = take (length xs) zs \<Longrightarrow> ys = drop (length xs) zs \<Longrightarrow> xs @ ys = zs"
  by (metis append_take_drop_id)

lemma heap_list_heap_update_list_id:
  assumes bound: "n \<le> addr_card"
  assumes lbs: "length bs = n"
  shows "(heap_list (heap_update_list a bs h) n a) = bs"
  using bound lbs
proof (induct n arbitrary: a bs h)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case
    apply (cases bs)
     apply clarsimp
    apply clarsimp
    by (metis (no_types, lifting) Suc_le_D Suc_le_eq add_cancel_right_right add_diff_cancel_left'
        fun_upd_same heap_update_list_value' linorder_not_less one_neq_zero plus_1_eq_Suc
        unat_minus_abs unsigned_1)
qed


lemma heap_update_list_nth_conv:
  "length bs \<le> addr_card \<Longrightarrow>
  heap_update_list a bs h a' =
   (if (unat a' + (if a' < a then addr_card else 0) - unat a) < length bs then
      bs ! (unat a' + (if a' < a then addr_card else 0)  - unat a)
   else
     h a')"
proof (induct bs arbitrary: a h)
  case Nil
  then show ?case by simp
next
  case (Cons b bs)
  from Cons.prems have bound: "Suc (length bs) \<le> addr_card" by simp
  hence bound': "length bs \<le> addr_card" by simp
  note hyp = Cons.hyps [OF this, of "a+1" " (h(a := b))"]
  show ?case
  proof (cases "a' < a")
    case True
    show ?thesis apply (simp add: hyp True)
      using True
      by (smt (verit) Nat.add_diff_assoc One_nat_def Suc_diff_Suc add_diff_cancel_left'
          cancel_comm_monoid_add_class.diff_cancel diff_add diff_diff_left
          diff_right_commute fun_upd_apply le_add_diff len_of_addr_card not_less_eq
          not_less_eq_eq nth_Cons_pos of_nat_add order_less_le trans_less_add2
          un_ui_le unat_0 unat_sub_if' unsigned_greater_eq unsigned_less word_less_def
          word_overflow_unat word_unat.Rep_inverse zero_less_diff)

  next
    case False
    show ?thesis apply (simp add: hyp False)
      using False bound'
      by (smt (verit) Nat.add_diff_assoc One_nat_def Suc_eq_plus1 Suc_le_eq
          add_diff_cancel_left bound cancel_comm_monoid_add_class.diff_cancel
          diff_zero fun_upd_def le_eq_less_or_eq len_of_addr_card linorder_not_le nth_Cons_0
          nth_Cons_Suc order_less_le plus_1_eq_Suc trans_le_add2 unatSuc2 unat_1
          unat_add_lem unat_mono unsigned_0 unsigned_less)
  qed
qed

lemma heap_update_list_overwrite_all_nth_conv:
  assumes lbs: "length bs = addr_card"
  shows "heap_update_list a bs h a' =
          bs ! (unat a' + (if a' < a then addr_card else 0)  - unat a)"
proof -
  from lbs have leq: "length bs \<le> addr_card" by simp
  show ?thesis
    using lbs
    apply (simp add: heap_update_list_nth_conv [OF leq])
    by (metis len_of_addr_card linorder_not_less unat_sub_if' unsigned_less word_less_nat_alt)
qed



lemma heap_update_list_overwrite':
  assumes bound: "length bs \<le> addr_card"
  assumes len_eq: "length bs = length bs'"
  shows "(heap_update_list a bs (heap_update_list a bs' h)) = (heap_update_list a bs h)"
  apply (rule ext)
  using bound len_eq
  apply (simp add: heap_update_list_nth_conv )
  done

lemma heap_list_tail_addr_card:
  assumes len: "length ys = addr_card"
  shows "heap_update_list p (xs @ ys) h = heap_update_list  (p + word_of_nat (length xs)) ys h"
proof -
  from len have len': "length ys \<le> addr_card" by simp
  show ?thesis
    apply (simp add: heap_update_list_concat_unfold)
    apply (rule ext)
    apply (simp add: heap_update_list_nth_conv [OF len'])
    using len
    by (metis len_of_addr_card linorder_not_less unat_sub_if' unsigned_less word_less_nat_alt)
qed

lemma heap_update_list_overwrite:
  assumes leq: "length bs = length bs'"
  shows "heap_update_list p bs (heap_update_list p bs' h) = heap_update_list p bs h"
proof (cases "length bs \<le> addr_card")
  case True
  from heap_update_list_overwrite' [OF True leq] show ?thesis by simp
next
  case False
  from False obtain xs ys where bs: "bs=xs@ys" and lys: "length ys = addr_card"
    by (metis append_take_drop_id diff_diff_cancel length_drop linorder_not_less order_less_le)
  from False leq obtain xs' ys' where bs': "bs'=xs'@ys'" and lys': "length ys' = addr_card"
    by (metis append_take_drop_id diff_diff_cancel length_drop linorder_not_less order_less_le)
  from lys have leq_ys: "length ys \<le> addr_card" by simp
  from lys' have leq_ys': "length ys' \<le> addr_card" by simp
  note eqs = heap_list_tail_addr_card [OF lys, where xs = xs]
    heap_list_tail_addr_card [OF lys', where xs = xs']
    heap_update_list_overwrite_all_nth_conv [OF lys]
    heap_update_list_overwrite_all_nth_conv [OF lys']

  show ?thesis
    apply (rule ext)
    apply (simp add: bs bs' eqs)
    done
qed

context xmem_type
begin


lemma xmem_type_is_value_byte_access_ti_update_ti_cancel:
  assumes i_bound: "i < size_of TYPE('a)"
  assumes lbs: "length bs = size_of TYPE('a)"
  assumes lbs': "length bs'= size_of TYPE('a)"
  assumes is_value: "is_value_byte (typ_uinfo_t TYPE('a)) i"
  shows "access_ti (typ_info_t TYPE('a)) (update_ti (typ_info_t TYPE('a)) bs v) bs' ! i = bs ! i"
  using is_value_byte_access_ti_update_ti_cancel [OF _ _ _ _ _  i_bound [simplified size_of_def]
      lbs [simplified size_of_def] lbs' [simplified size_of_def] is_value [simplified typ_uinfo_t_def]]
  by (simp add: local.wf_component_descs local.wf_field_descs wf_fdp_fd(1) wf_lf_fdp)

lemma xmem_type_is_value_byte_access_ti_id:
  assumes i_bound: "i < size_of TYPE('a)"
  assumes lbs: "length bs = size_of TYPE('a)"
  assumes is_value: "is_value_byte (typ_uinfo_t TYPE('a)) i"
  shows "access_ti (typ_info_t TYPE('a)) v (bs[i:=b]) = access_ti (typ_info_t TYPE('a)) v bs"
  using is_value_byte_access_ti_id  [OF _ _ _ _ _  i_bound [simplified size_of_def]
      lbs [simplified size_of_def] is_value [simplified typ_uinfo_t_def]]
    by (simp add: local.wf_component_descs local.wf_field_descs wf_fdp_fd(1) wf_lf_fdp)


lemma is_padding_byte_to_lense: "is_padding_byte (typ_uinfo_t TYPE('a)) i
 \<Longrightarrow> lense.is_padding_byte i"
  by (metis is_padding_byte_def local.lense.complement local.lense.is_padding_byte_def
      local.lense.is_value_byte_update_depends local.xmem_type_is_padding_byte_update_ti_id size_of_def typ_uinfo_size)

lemma is_value_byte_to_lense: "is_value_byte (typ_uinfo_t TYPE('a)) i
 \<Longrightarrow> lense.is_value_byte i"
  using xmem_type_is_padding_byte_access_ti
 xmem_type_is_padding_byte_update_ti_id xmem_type_is_value_byte_access_ti_update_ti_cancel
  using is_value_byte_def local.lense.is_value_byteI local.size_of_def
    xmem_type_is_value_byte_access_ti_id by auto

lemma is_padding_byte_from_lense:
 assumes padding: "lense.is_padding_byte i"
 shows  "is_padding_byte (typ_uinfo_t TYPE('a)) i"
proof -
  from padding have i_sz: "i < size_of (TYPE('a))"
    using local.lense.is_padding_byte_def by blast
  show ?thesis
  proof (cases "is_padding_byte (typ_uinfo_t TYPE('a)) i")
    case True
    then show ?thesis by simp
  next
    case False
    with complement_tu_padding [OF i_sz [simplified size_of_def, simplified typ_uinfo_size [symmetric]]] show ?thesis
      using i_sz is_value_byte_to_lense local.lense.complement padding by blast
  qed
qed

lemma is_padding_byte_lense_conv: "is_padding_byte (typ_uinfo_t TYPE('a)) i = lense.is_padding_byte i"
  using is_padding_byte_from_lense is_padding_byte_to_lense by blast

lemma is_value_byte_from_lense:
 assumes is_value: "lense.is_value_byte i"
 shows  "is_value_byte (typ_uinfo_t TYPE('a)) i"
proof -
  from is_value have i_sz: "i < size_of (TYPE('a))"
    using local.lense.is_value_byte_def by blast
  show ?thesis
  proof (cases "is_value_byte (typ_uinfo_t TYPE('a)) i")
    case True
    then show ?thesis by simp
  next
    case False
    with complement_tu_padding [OF i_sz [simplified size_of_def, simplified typ_uinfo_size [symmetric]]] show ?thesis
      using assms i_sz is_padding_byte_to_lense local.lense.complement by blast
  qed
qed

lemma is_value_byte_lense_conv: "is_value_byte (typ_uinfo_t TYPE('a)) i = lense.is_value_byte i"
  using is_value_byte_from_lense is_value_byte_to_lense by blast

lemma eq_padding_lense_conv: "eq_padding (typ_uinfo_t TYPE('a)) bs bs' = lense.eq_padding bs bs'"
  apply (simp add:  lense.eq_padding_is_padding_byte_conv eq_padding_def)
  by (simp add: is_padding_byte_lense_conv size_of_def)


lemma eq_upto_padding_lense_conv: "eq_upto_padding (typ_uinfo_t TYPE('a)) bs bs' = lense.eq_upto_padding bs bs'"
  apply (simp add:  lense.eq_upto_padding_is_value_byte_conv eq_upto_padding_def)
  by (simp add: is_value_byte_lense_conv size_of_def)

lemma lense_eq_upto_padding_from_bytes_eq:
  assumes eq_upto_padding: "lense.eq_upto_padding bs bs'"
  shows "((from_bytes bs)::'a) = from_bytes bs'"
  using eq_upto_padding
  by (metis field_desc.select_convs(2) field_desc_def from_bytes_def local.field_sz_size_of
      local.field_update_update_ti local.xmem_type_wf_field_desc.eq_upto_padding_upd
      padding_base.eq_upto_padding_length_eq update_ti_t_def)

lemma eq_upto_padding_from_bytes_eq:
  assumes eq_upto_padding: "eq_upto_padding (typ_uinfo_t TYPE('a)) bs bs'"
  shows "((from_bytes bs)::'a) = from_bytes bs'"
  using lense_eq_upto_padding_from_bytes_eq eq_upto_padding_lense_conv eq_upto_padding
  by (simp add: typ_uinfo_t_def)

lemma lense_eq_padding_to_bytes_eq:
  assumes eq_padding: "lense.eq_padding bs bs'"
  shows "(to_bytes (v::'a) bs) = to_bytes v bs'"
proof -
  from lense.eq_padding_acc [OF eq_padding]
  show ?thesis
    by (simp add: to_bytes_def)
qed

lemma eq_padding_to_bytes_eq:
  assumes eq_padding: "eq_padding (typ_uinfo_t TYPE('a)) bs bs'"
  shows "(to_bytes (v::'a) bs) = to_bytes v bs'"
  using lense_eq_padding_to_bytes_eq eq_padding_lense_conv eq_padding
  by (simp add: typ_uinfo_t_def)


lemma eq_padding_to_bytes:
  "length bs = size_of TYPE('a) \<Longrightarrow> eq_padding (typ_uinfo_t TYPE('a)) (to_bytes (v::'a) bs) bs"
  by (simp add: eq_padding_lense_conv local.lense.field_access_eq_padding1 to_bytes_def)

lemma lense_eq_padding_to_bytes:
  "length bs = size_of TYPE('a) \<Longrightarrow> lense.eq_padding (to_bytes (v::'a) bs) bs"
  using eq_padding_to_bytes eq_padding_lense_conv
  by simp

lemma heap_list_heap_update_id:
  fixes p::"'a ptr"
  shows "(heap_list
            (heap_update_list (ptr_val p)
               (to_bytes (u::'a) (heap_list h (size_of TYPE('a)) (ptr_val p))) h)
            (size_of TYPE('a)) (ptr_val p)) =
         (to_bytes u (heap_list h (size_of TYPE('a)) (ptr_val p)))"
proof -
  have bound: "size_of TYPE('a) \<le> addr_card"
    using max_size nless_le by blast
  have lbs: "length (to_bytes u (heap_list h (size_of TYPE('a)) (ptr_val p))) = size_of TYPE('a)"
    by (simp add: local.lense.access_result_size to_bytes_def)
  note eq1 = heap_list_heap_update_list_id [OF bound lbs]
  show ?thesis
    by (simp add: eq1)
qed

lemma heap_update_collapse:
  fixes p::"'a ptr"
  shows "heap_update p v (heap_update p u h) = heap_update p v h"
proof -

  have lv: "length (to_bytes v (to_bytes u (heap_list h (size_of TYPE('a)) (ptr_val p)))) =
              size_of TYPE('a)"
    by (simp add: local.lense.access_result_size to_bytes_def)

  have lu: "length (to_bytes u (heap_list h (size_of TYPE('a)) (ptr_val p))) = size_of TYPE('a)"
    by (simp add: local.lense.access_result_size to_bytes_def)
  have leq: "length (to_bytes v (to_bytes u (heap_list h (size_of TYPE('a)) (ptr_val p)))) =
        length (to_bytes u (heap_list h (size_of TYPE('a)) (ptr_val p)))"
    by (simp add: lv lu)
  have eq:
    "(to_bytes v (to_bytes u (heap_list h (size_of TYPE('a)) (ptr_val p)))) =
        (to_bytes v (heap_list h (size_of TYPE('a)) (ptr_val p)))"
    by (metis eq_padding_lense_conv eq_padding_to_bytes_eq heap_list_length
        local.lense.field_access_eq_padding1 to_bytes_def)
  show ?thesis
    apply (simp add: heap_update_def)
    apply (simp add: heap_list_heap_update_id [OF ])
    apply (subst heap_update_list_overwrite [OF leq])
    apply (simp add: eq)
    done
qed

lemma heap_update_padding_collapse:
  fixes p::"'a ptr"
  assumes lbs: "length bs = size_of TYPE('a)"
  assumes lbs': "length bs' = size_of TYPE('a)"
  shows "heap_update_padding p v bs (heap_update_padding p u bs' h) = heap_update_padding p v bs h"
  apply (simp add: heap_update_padding_def)
  using lbs lbs' heap_update_list_overwrite
  by auto

lemma heap_update_padding_heap_update_collapse:
  fixes p::"'a ptr"
  assumes lbs: "length bs = size_of TYPE('a)"
  shows "heap_update_padding p v bs (heap_update p u h) = heap_update_padding p v bs h"
  by (simp add: heap_update_heap_update_padding_conv  heap_update_padding_collapse [OF lbs])

lemma to_bytes_from_bytes_id:
  "length bs = size_of TYPE('a) \<Longrightarrow> to_bytes ((from_bytes bs)::'a) bs  = bs"
  by (metis (no_types, lifting) field_desc.select_convs(2) field_desc_def from_bytes_def lense_eq_padding_to_bytes
      local.field_sz_size_of local.field_sz_size_td local.lense.eq_upto_paddingI
      local.lense.padding_eq_complement local.lense.update_access local.upd
      padding_base.eq_padding_length1 to_bytes_def update_ti_update_ti_t)


lemma to_bytes_heap_list_id:
  "to_bytes ((from_bytes (heap_list h (size_of TYPE('a)) a))::'a)
         (heap_list h (size_of TYPE('a)) a) =
   heap_list h (size_of TYPE('a)) a"
  by (simp add: to_bytes_from_bytes_id)


lemma heap_update_id:
  fixes p::"'a ptr"
  shows "heap_update p (h_val h p) h = h"
  by (simp add: heap_update_def h_val_def to_bytes_heap_list_id heap_update_list_id')

context
  fixes s f n
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
begin
  interpretation flense: padding_lense "access_ti s" "update_ti s" "size_td s"
    using field_lookup_padding_lense [OF fl] .

private lemma n_t:  "n < size_of TYPE('a)"
  using fl
  by (metis add_diff_cancel_right' add_leD2 cancel_comm_monoid_add_class.diff_cancel field_lookup_offset_size'
      field_lookup_wf_size_desc_gt
      local.field_sz_size_of local.field_sz_size_td local.wf_size_desc nat_less_le not_add_less2)

private lemma wf_desc_s: "wf_desc s"
  using fl field_lookup_wf_desc_pres(1) local.wf_desc by blast

private lemma wf_size_desc_s: "wf_size_desc s"
  using fl field_lookup_wf_size_desc_pres(1) local.wf_size_desc by blast

private lemma wf_field_descs_s: "wf_field_descs (set (field_descs s))"
  using fl local.field_lookup_wf_field_descs by blast

private lemma wf_component_descs_s: "wf_component_descs s"
  using fl local.field_lookup_wf_component_descs by blast

private lemma wf_fd_s: "wf_fd s"
  using fl local.wf_desc local.wf_lf wf_fd_field_lookupD wf_fdp_fd(1) wf_lf_fdp
  by blast

lemma xmem_type_field_lookup_is_padding_byte_focus:
  assumes i_lower: "n \<le> i"
  assumes i_upper :"i < n + size_td s"
  shows "is_padding_byte (typ_uinfo_t TYPE('a)) i = is_padding_byte (export_uinfo s) (i - n)"
  using field_lookup_is_padding_byte_focus [OF fl i_lower i_upper]
  by (simp add: typ_uinfo_t_def)

lemma xmem_type_field_lookup_is_padding_byte_focus_rev1:
  assumes is_padding: "is_padding_byte (export_uinfo s) i"
  shows "is_padding_byte (typ_uinfo_t TYPE('a)) (i + n)"
proof -
  from is_padding have i_s: "i < size_td s"
    using is_padding_byte_def by simp
  have lower: "n \<le> i + n" by simp
  from i_s have upper: "i + n < n + size_td s" by simp

  from xmem_type_field_lookup_is_padding_byte_focus [OF lower upper] is_padding
  show ?thesis by simp
qed

lemma xmem_type_field_lookup_is_padding_byte_focus_rev2:
  assumes is_padding: "is_padding_byte (typ_uinfo_t TYPE('a)) (i + n)"
  assumes i_bound: "i < size_td s"
  shows "is_padding_byte (export_uinfo s) i"
  proof -
    have lower: "n \<le> i + n" by simp
    from i_bound have upper: "i + n < n + size_td s" by simp
    from xmem_type_field_lookup_is_padding_byte_focus [OF lower upper] is_padding
    show ?thesis
      by simp
  qed


lemma xmem_type_field_lookup_lense_is_padding_byte_focus_rev1:
  assumes is_padding: "flense.is_padding_byte i"
  shows "lense.is_padding_byte  (i + n)"
proof -
  from is_padding have i_s: "i < size_td s"
    using flense.is_padding_byte_def by simp
  have lower: "n \<le> i + n" by simp
  from i_s have upper: "i + n < n + size_td s" by simp

  from field_lookup_is_padding_byte_inner_to_outer [OF fl lower upper] is_padding
  show ?thesis by (simp add: size_of_def)
qed

lemma xmem_type_field_lookup_lense_is_padding_byte_focus_rev2:
  assumes is_padding: "lense.is_padding_byte  (i + n)"
  assumes i_bound: "i < size_td s"
  shows "flense.is_padding_byte  i"
  proof -
    have lower: "n \<le> i + n" by simp
    from i_bound have upper: "i + n < n + size_td s" by simp
    from field_lookup_is_padding_byte_outer_to_inner [OF fl lower upper] is_padding
    show ?thesis
      by (simp add: size_of_def)
  qed

lemma xmem_type_field_lookup_is_value_byte_focus:
  assumes i_lower: "n \<le> i"
  assumes i_upper :"i < n + size_td s"
  shows "is_value_byte (typ_uinfo_t TYPE('a)) i = is_value_byte (export_uinfo s) (i - n)"
  using field_lookup_is_value_byte_focus [OF fl i_lower i_upper]
  by (simp add: typ_uinfo_t_def)

lemma xmem_type_field_lookup_is_value_byte_focus_rev1:
  assumes is_value: "is_value_byte (export_uinfo s) i"
  shows "is_value_byte (typ_uinfo_t TYPE('a)) (i + n)"
proof -
  from is_value have i_s: "i < size_td s"
    using is_value_byte_def by simp
  have lower: "n \<le> i + n" by simp
  from i_s have upper: "i + n < n + size_td s" by simp

  from xmem_type_field_lookup_is_value_byte_focus [OF lower upper] is_value
  show ?thesis by simp
qed

lemma xmem_type_field_lookup_is_value_byte_focus_rev2:
  assumes is_value: "is_value_byte (typ_uinfo_t TYPE('a)) (i + n)"
  assumes i_bound: "i < size_td s"
  shows "is_value_byte (export_uinfo s) i"
  proof -
    have lower: "n \<le> i + n" by simp
    from i_bound have upper: "i + n < n + size_td s" by simp
    from xmem_type_field_lookup_is_value_byte_focus [OF lower upper] is_value
    show ?thesis
      by simp
  qed


lemma xmem_type_field_lookup_lense_is_value_byte_focus_rev1:
  assumes is_value: "flense.is_value_byte i"
  shows "lense.is_value_byte (i + n)"
proof -
  from is_value have i_s: "i < size_td s"
    using flense.is_value_byte_def by simp
  have lower: "n \<le> i + n" by simp
  from i_s have upper: "i + n < n + size_td s" by simp

  from field_lookup_is_value_byte_inner_to_outer [OF fl lower upper] is_value
  show ?thesis by (simp add: size_of_def)
qed

lemma xmem_type_field_lookup_lense_is_value_byte_focus_rev2:
  assumes is_value: "lense.is_value_byte (i + n)"
  assumes i_bound: "i < size_td s"
  shows "flense.is_value_byte i"
  proof -
    have lower: "n \<le> i + n" by simp
    from i_bound have upper: "i + n < n + size_td s" by simp
    from field_lookup_is_value_byte_outer_to_inner [OF fl lower upper] is_value
    show ?thesis
      by (simp add: size_of_def)
  qed


lemma field_lookup_is_padding_byte_access_ti:
  assumes i_bound: "i < size_td s"
  assumes lbs: "length bs = size_td s"
  assumes is_padding: "is_padding_byte (export_uinfo s) i"
  shows "access_ti s v bs ! i = bs ! i"
  using is_padding_byte_access_ti [OF wf_desc_s wf_size_desc_s wf_field_descs_s
      wf_component_descs_s wf_fd_s i_bound lbs is_padding] .

lemma field_lookup_is_padding_byte_update_ti_id:
  assumes i_bound: "i < size_td s"
  assumes lbs: "length bs = size_td s"
  assumes is_padding: "is_padding_byte (export_uinfo s) i"
  shows "update_ti s (bs[i := b]) v = update_ti s bs v"
  using is_padding_byte_update_ti_id [OF wf_desc_s wf_size_desc_s wf_field_descs_s
      wf_component_descs_s wf_fd_s i_bound lbs is_padding] .

lemma field_lookup_is_value_byte_access_ti_update_ti_cancel:
  assumes i_bound: "i < size_td s"
  assumes lbs: "length bs = size_td s"
  assumes lbs': "length bs' = size_td s"
  assumes is_value: "is_value_byte (export_uinfo s) i"
  shows "access_ti s (update_ti s bs v) bs' ! i = bs ! i"
using is_value_byte_access_ti_update_ti_cancel  [OF wf_desc_s wf_size_desc_s wf_field_descs_s
      wf_component_descs_s wf_fd_s i_bound lbs lbs' is_value] .

lemma field_lookup_is_value_byte_access_ti_id:
  assumes i_bound: "i < size_td s"
  assumes lbs: "length bs = size_td s"
  assumes is_value: "is_value_byte (export_uinfo s) i"
  shows "access_ti s v (bs[i := b]) = access_ti s v bs"
using is_value_byte_access_ti_id [OF wf_desc_s wf_size_desc_s wf_field_descs_s
      wf_component_descs_s wf_fd_s i_bound lbs is_value] .

lemma field_lookup_is_padding_byte_to_lense:
  assumes is_padding: "is_padding_byte (export_uinfo s) i"
  shows "flense.is_padding_byte i"
proof (rule flense.is_padding_byteI)
  from is_padding show "i < size_td s"
    using is_padding_byte_def by simp
next
  fix v::'a and bs::"byte list"
  assume i_bound: "i < size_td s"
  assume lbs:  "length bs = size_td s"
  show "access_ti s v bs ! i = bs ! i"
    by (rule field_lookup_is_padding_byte_access_ti [OF i_bound lbs is_padding])
next
  fix v::'a and bs::"byte list" and b::"byte"
  assume i_bound: "i < size_td s"
  assume lbs:  "length bs = size_td s"
  show "update_ti s bs v = update_ti s (bs[i := b]) v"
    using field_lookup_is_padding_byte_update_ti_id [OF i_bound lbs is_padding] by simp
qed

lemma field_lookup_is_padding_byte_from_lense:
  assumes is_padding: "flense.is_padding_byte i"
  shows "is_padding_byte (export_uinfo s) i"
proof -
  from is_padding have i_bound: "i < size_td s" by (simp add: flense.is_padding_byte_def)
  from xmem_type_field_lookup_lense_is_padding_byte_focus_rev1 [OF is_padding]
  have "lense.is_padding_byte (i + n)".
  from is_padding_byte_from_lense [OF this]
  have "is_padding_byte (typ_uinfo_t TYPE('a)) (i + n)".
  with xmem_type_field_lookup_is_padding_byte_focus [where i="i + n"] i_bound
  show ?thesis by simp
qed

lemma field_lookup_is_padding_byte_lense_conv:
"is_padding_byte (export_uinfo s) i \<longleftrightarrow> flense.is_padding_byte i"
  using field_lookup_is_padding_byte_from_lense field_lookup_is_padding_byte_to_lense
  by blast

lemma field_lookup_is_value_byte_from_lense:
  assumes is_value: "flense.is_value_byte i"
  shows "is_value_byte (export_uinfo s) i"
proof -
  from is_value have i_bound: "i < size_td s" by (simp add: flense.is_value_byte_def)
  from xmem_type_field_lookup_lense_is_value_byte_focus_rev1 [OF is_value]
  have "lense.is_value_byte (i + n)".
  from is_value_byte_from_lense [OF this]
  have "is_value_byte (typ_uinfo_t TYPE('a)) (i + n)".
  with xmem_type_field_lookup_is_value_byte_focus [where i="i + n"] i_bound
  show ?thesis by simp
qed

lemma field_lookup_is_value_byte_to_lense:
  assumes is_value: "is_value_byte (export_uinfo s) i"
  shows "flense.is_value_byte i"
proof (rule flense.is_value_byteI)
  from is_value show "i < size_td s"
    using is_value_byte_def by simp
next
  fix v::'a and bs::"byte list" and bs'::"byte list"
  assume i_bound: "i < size_td s"
  assume lbs:  "length bs = size_td s"
  assume lbs':  "length bs' = size_td s"
  show "access_ti s (update_ti s bs v) bs' ! i = bs ! i"
    by (rule field_lookup_is_value_byte_access_ti_update_ti_cancel [OF i_bound lbs lbs' is_value])
next
  fix v::'a and bs::"byte list" and b::"byte"
  assume i_bound: "i < size_td s"
  assume lbs:  "length bs = size_td s"
  show "access_ti s v bs = access_ti s v (bs[i := b])"
    using field_lookup_is_value_byte_access_ti_id [OF i_bound lbs is_value] by simp
qed

lemma field_lookup_is_value_byte_lense_conv:
"is_value_byte (export_uinfo s) i \<longleftrightarrow> flense.is_value_byte i"
  using field_lookup_is_value_byte_from_lense field_lookup_is_value_byte_to_lense
  by blast

lemma field_lookup_eq_padding_lense_conv: "eq_padding (export_uinfo s) bs bs' \<longleftrightarrow> flense.eq_padding bs bs'"
  using field_lookup_is_padding_byte_lense_conv
  by (simp add: eq_padding_def flense.eq_padding_is_padding_byte_conv)

lemma field_lookup_eq_upto_padding_lense_conv: "eq_upto_padding (export_uinfo s) bs bs' \<longleftrightarrow> flense.eq_upto_padding bs bs'"
  using field_lookup_is_value_byte_lense_conv
  by (simp add: eq_upto_padding_def flense.eq_upto_padding_is_value_byte_conv)

lemma xmem_type_field_lookup_eq_padding_focus:
assumes lbs: "length bs = size_of TYPE('a)"
assumes lbs': "length bs' = size_of TYPE('a)"
assumes eq_padding: "eq_padding (typ_uinfo_t TYPE('a)) bs bs'"
shows "eq_padding (export_uinfo s) (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
  using field_lookup_eq_padding_focus [OF fl lbs [simplified size_of_def] lbs'[simplified size_of_def] _ _
    eq_padding [simplified typ_uinfo_t_def] ]
  by (simp add: typ_uinfo_t_def size_of_def)

lemma xmem_type_field_lookup_eq_padding_focus_eq:
assumes lbs: "length bs = size_of TYPE('a)"
assumes lbs': "length bs' = size_of TYPE('a)"
assumes pfx_eq: "\<And>i. i < n \<Longrightarrow> bs ! i = bs' ! i"
assumes sfx_eq: "\<And>i. n + size_td s \<le> i \<Longrightarrow> i < size_of TYPE('a) \<Longrightarrow> bs ! i = bs' ! i"
shows "eq_padding (typ_uinfo_t TYPE('a)) bs bs' =
      eq_padding (export_uinfo s) (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
  using field_lookup_eq_padding_focus_eq [OF fl lbs [simplified size_of_def] lbs'[simplified size_of_def] pfx_eq sfx_eq]
  by (simp add: typ_uinfo_t_def size_of_def)

lemma xmem_type_field_lookup_lense_eq_padding_focus:
assumes lbs: "length bs = size_of TYPE('a)"
assumes lbs': "length bs' = size_of TYPE('a)"
assumes eq_padding: "lense.eq_padding bs bs'"
shows "flense.eq_padding (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
  using xmem_type_field_lookup_eq_padding_focus [OF lbs lbs'] eq_padding
    eq_padding_lense_conv field_lookup_eq_padding_lense_conv
  by simp

lemma xmem_type_field_lookup_lense_eq_padding_focus_eq:
assumes lbs: "length bs = size_of TYPE('a)"
assumes lbs': "length bs' = size_of TYPE('a)"
assumes pfx_eq: "\<And>i. i < n \<Longrightarrow> bs ! i = bs' ! i"
assumes sfx_eq: "\<And>i. n + size_td s \<le> i \<Longrightarrow> i < size_of TYPE('a) \<Longrightarrow> bs ! i = bs' ! i"
shows "lense.eq_padding bs bs' =
      flense.eq_padding (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
  using xmem_type_field_lookup_eq_padding_focus_eq [OF lbs lbs' pfx_eq sfx_eq]
    eq_padding_lense_conv field_lookup_eq_padding_lense_conv
  by simp

lemma xmem_type_field_lookup_eq_upto_padding_focus:
assumes lbs: "length bs = size_of TYPE('a)"
assumes lbs': "length bs' = size_of TYPE('a)"
assumes eq_upto_padding: "eq_upto_padding (typ_uinfo_t TYPE('a)) bs bs'"
shows "eq_upto_padding (export_uinfo s) (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
  using field_lookup_eq_upto_padding_focus [OF fl lbs [simplified size_of_def] lbs'[simplified size_of_def] _ _
      eq_upto_padding [simplified typ_uinfo_t_def] ]
  by (simp add: typ_uinfo_t_def size_of_def)

lemma xmem_type_field_lookup_eq_upto_padding_focus_eq:
assumes lbs: "length bs = size_of TYPE('a)"
assumes lbs': "length bs' = size_of TYPE('a)"
assumes pfx_eq: "\<And>i. i < n \<Longrightarrow> bs ! i = bs' ! i"
assumes sfx_eq: "\<And>i. n + size_td s \<le> i \<Longrightarrow> i < size_of TYPE('a) \<Longrightarrow> bs ! i = bs' ! i"
shows "eq_upto_padding (typ_uinfo_t TYPE('a)) bs bs' =
      eq_upto_padding (export_uinfo s) (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
  using field_lookup_eq_upto_padding_focus_eq [OF fl lbs [simplified size_of_def] lbs'[simplified size_of_def] pfx_eq sfx_eq]
  by (simp add: typ_uinfo_t_def size_of_def)

lemma xmem_type_field_lookup_lense_eq_upto_padding_focus:
assumes lbs: "length bs = size_of TYPE('a)"
assumes lbs': "length bs' = size_of TYPE('a)"
assumes eq_upto_padding: "lense.eq_upto_padding bs bs'"
shows "flense.eq_upto_padding (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
  using xmem_type_field_lookup_eq_upto_padding_focus [OF lbs lbs'] eq_upto_padding
    eq_upto_padding_lense_conv field_lookup_eq_upto_padding_lense_conv
  by simp

lemma xmem_type_field_lookup_lense_eq_upto_padding_focus_eq:
assumes lbs: "length bs = size_of TYPE('a)"
assumes lbs': "length bs' = size_of TYPE('a)"
assumes pfx_eq: "\<And>i. i < n \<Longrightarrow> bs ! i = bs' ! i"
assumes sfx_eq: "\<And>i. n + size_td s \<le> i \<Longrightarrow> i < size_of TYPE('a) \<Longrightarrow> bs ! i = bs' ! i"
shows "lense.eq_upto_padding bs bs' =
      flense.eq_upto_padding (take (size_td s) (drop n bs)) (take (size_td s) (drop n bs'))"
  using xmem_type_field_lookup_eq_upto_padding_focus_eq [OF lbs lbs' pfx_eq sfx_eq]
    eq_upto_padding_lense_conv field_lookup_eq_upto_padding_lense_conv
  by simp

lemma xmem_type_field_lookup_eq_padding_super_update_bs:
  assumes lxbs: "length xbs = size_of TYPE('a)"
  assumes lbs: "length bs = size_td s"
  assumes lbs': "length bs' = size_td s"
  shows "eq_padding (typ_uinfo_t TYPE('a)) (super_update_bs bs xbs n) (super_update_bs bs' xbs n) \<longleftrightarrow>
             eq_padding (export_uinfo s) bs bs'"
  using field_lookup_eq_padding_super_update_bs [OF fl lxbs [simplified size_of_def] lbs lbs']
  by (simp add: typ_uinfo_t_def)

lemma xmem_type_field_lookup_lense_eq_padding_super_update_bs:
  assumes lxbs: "length xbs = size_of TYPE('a)"
  assumes lbs: "length bs = size_td s"
  assumes lbs': "length bs' = size_td s"
  shows "lense.eq_padding (super_update_bs bs xbs n) (super_update_bs bs' xbs n) \<longleftrightarrow>
           flense.eq_padding bs bs'"
  using xmem_type_field_lookup_eq_padding_super_update_bs [OF lxbs lbs lbs']
    eq_padding_lense_conv field_lookup_eq_padding_lense_conv
  by simp

lemma xmem_type_field_lookup_eq_upto_padding_super_update_bs:
  assumes lxbs: "length xbs = size_of TYPE('a)"
  assumes lbs: "length bs = size_td s"
  assumes lbs': "length bs' = size_td s"
  shows "eq_upto_padding (typ_uinfo_t TYPE('a)) (super_update_bs bs xbs n) (super_update_bs bs' xbs n) \<longleftrightarrow>
             eq_upto_padding (export_uinfo s) bs bs'"
  using field_lookup_eq_upto_padding_super_update_bs [OF fl lxbs [simplified size_of_def] lbs lbs']
  by (simp add: typ_uinfo_t_def)

lemma xmem_type_field_lookup_lense_eq_upto_padding_super_update_bs:
  assumes lxbs: "length xbs = size_of TYPE('a)"
  assumes lbs: "length bs = size_td s"
  assumes lbs': "length bs' = size_td s"
  shows "lense.eq_upto_padding (super_update_bs bs xbs n) (super_update_bs bs' xbs n) \<longleftrightarrow>
           flense.eq_upto_padding bs bs'"
  using xmem_type_field_lookup_eq_upto_padding_super_update_bs [OF lxbs lbs lbs']
    eq_upto_padding_lense_conv field_lookup_eq_upto_padding_lense_conv
  by simp

lemma access_ti_update_ti_lense_eq_upto_padding:
  assumes lbs: "length bs = size_td s"
  assumes lbs': "length bs' = size_td s"
  shows "flense.eq_upto_padding (access_ti s (update_ti s bs v) bs') bs"
  by (simp add: flense.value_byte_to_eq_upto_padding_eq lbs lbs' length_fa_ti
      flense.is_value_byte_acc_upd_cancel wf_fd_s)

lemma access_ti_update_ti_eq_upto_padding:
  assumes lbs: "length bs = size_td s"
  assumes lbs': "length bs' = size_td s"
  shows "eq_upto_padding (export_uinfo s) (access_ti s (update_ti s bs v) bs') bs"
  using access_ti_update_ti_lense_eq_upto_padding [OF lbs lbs']
    field_lookup_eq_upto_padding_lense_conv
  by simp

lemma access_ti_update_ti_lense_eq_padding:
  assumes "flense.eq_padding bs bs'"
  shows "access_ti s (update_ti s bs v) bs' = bs"
  by (metis (no_types, lifting) access_ti_update_ti_lense_eq_upto_padding assms flense.field_access_eq_padding1
      flense.padding_eq_complement padding_base.eq_padding_length1
      flense.eq_padding_length2 flense.eq_padding_trans)

lemma access_ti_update_ti_eq_padding:
  assumes "eq_padding (export_uinfo s) bs bs'"
  shows "access_ti s (update_ti s bs v) bs' = bs"
  using access_ti_update_ti_lense_eq_padding assms field_lookup_eq_padding_lense_conv
  by simp

lemma
  assumes match: "export_uinfo s = typ_uinfo_t TYPE('b::xmem_type)"
  assumes lbs: "length bs = size_td s"
  shows "access_ti s v bs = to_bytes ((from_bytes (access_ti s v bs))::'b) bs"
proof -

  from match
  have sz_acc_s: "length (access_ti s v bs) = size_td (typ_info_t TYPE('b))"
    by (metis export_size_of flense.access_result_size fold_typ_uinfo_t)
  show ?thesis
    by (smt (verit, best) field_lookup_eq_padding_lense_conv flense.field_access_eq_padding1
        lbs match sz_acc_s xmem_type_class.eq_padding_lense_conv xmem_type_class.field_sz_size_of
        xmem_type_class.field_sz_size_td xmem_type_class.lense_eq_padding_to_bytes_eq
        xmem_type_class.to_bytes_from_bytes_id)
qed

context
  assumes match: "export_uinfo s = typ_uinfo_t TYPE('b::xmem_type)"
begin

lemma field_lookup_lense_eq_padding_fieldtyp_conv:
  "flense.eq_padding bs bs' = xmem_type_class.lense.eq_padding TYPE('b) bs bs'"
  using field_lookup_eq_padding_lense_conv match xmem_type_class.eq_padding_lense_conv by auto

lemma field_lookup_lense_eq_upto_padding_fieldtyp_conv:
  "flense.eq_upto_padding bs bs' = xmem_type_class.lense.eq_upto_padding TYPE('b) bs bs'"
  using field_lookup_eq_upto_padding_lense_conv match xmem_type_class.eq_upto_padding_lense_conv by auto

lemma field_lookup_is_value_byte_fieldtyp_conv:
  "flense.is_value_byte i = xmem_type_class.lense.is_value_byte TYPE('b) i"
  using field_lookup_is_value_byte_lense_conv match xmem_type_class.is_value_byte_lense_conv by auto

lemma field_lookup_is_padding_byte_fieldtyp_conv:
  "flense.is_padding_byte i = xmem_type_class.lense.is_padding_byte TYPE('b) i"
  using field_lookup_is_padding_byte_lense_conv match xmem_type_class.is_padding_byte_lense_conv by auto


lemma field_lookup_access_ti_to_bytes_field_conv:
  assumes eq_upto_padding: "eq_upto_padding (export_uinfo s) (access_ti s v bs) vs"
  assumes eq_padding: "eq_padding (export_uinfo s) bs bs'"
  shows "access_ti s v bs = to_bytes ((from_bytes vs)::'b) bs'"
proof -
  from eq_upto_padding have flense_eq_upto: "flense.eq_upto_padding (access_ti s v bs) vs"
    by (simp add: field_lookup_eq_upto_padding_lense_conv)
  hence blense_eq_upto: "xmem_type_class.lense.eq_upto_padding TYPE('b) (access_ti s v bs) vs"
    by (simp add: field_lookup_lense_eq_upto_padding_fieldtyp_conv)

  from eq_padding have flense_eq: "flense.eq_padding bs bs'"
    by (simp add: field_lookup_eq_padding_lense_conv)
  hence blense_eq: "xmem_type_class.lense.eq_padding TYPE('b) bs bs'"
    by (simp add: field_lookup_lense_eq_padding_fieldtyp_conv)

  show ?thesis
    using flense_eq flense_eq_upto blense_eq blense_eq_upto

    apply (simp add: to_bytes_def from_bytes_def c_type_class.to_bytes_def c_type_class.from_bytes_def)
    by (smt (verit, ccfv_threshold) c_type_class.to_bytes_def field_lookup_lense_eq_padding_fieldtyp_conv
        flense.eq_padding_length1 flense.field_access_eq_padding1 padding_base.eq_upto_padding_length2
        update_ti_s_from_bytes xmem_type_class.lense.eq_padding_acc xmem_type_class.lense_eq_upto_padding_from_bytes_eq
        xmem_type_class.to_bytes_from_bytes_id)
qed

lemma field_lookup_access_ti_eq_upto_padding:
  "length bs = size_td s \<Longrightarrow>
  eq_upto_padding (export_uinfo s) (access_ti s v bs) (access_ti s v bs')"
  by (metis access_ti_update_ti_eq_upto_padding flense.access_result_size flense.update_access)

lemma field_lookup_access_ti_eq_padding_value:
  "length bs = size_td s \<Longrightarrow> eq_padding (export_uinfo s) (access_ti s v bs) (access_ti s v' bs)"
  by (meson eq_padding_sym eq_padding_trans field_lookup_eq_padding_lense_conv flense.field_access_eq_padding1)

lemma field_lookup_access_ti_eq_padding_bytes:
  "length bs = size_td s \<Longrightarrow> eq_padding (export_uinfo s) (access_ti s v bs) bs"
  using field_lookup_eq_padding_lense_conv flense.field_access_eq_padding1 by blast

lemma field_lookup_access_ti_to_bytes_field_conv':
  assumes eq_upto_padding: "eq_upto_padding (export_uinfo s) (access_ti s v bs) vs"
  assumes lbs: "length bs = size_td s"
  shows "access_ti s v bs = to_bytes ((from_bytes vs)::'b) bs"
  using field_lookup_access_ti_to_bytes_field_conv [OF eq_upto_padding eq_padding_refl] lbs
  by simp


lemma field_lookup_update_ti_from_bytes_field_conv:
  fixes v::'a and vf::'b
  assumes lbs: "length bs = size_td s"
  assumes lxbs: "length xbs = size_of TYPE('a)"
  shows "update_ti (typ_info_t TYPE('b)) bs vf =
           (from_bytes (access_ti s (update_ti s bs v) xbs)) "
proof -
  from lbs lxbs
  have "eq_upto_padding (export_uinfo s) (access_ti s (update_ti s bs v) xbs) bs"
    by (metis access_ti_update_ti_eq_upto_padding access_ti_update_ti_lense_eq_padding
        flense.access_result_size flense.eq_padding_refl flense.update_access)

  hence "from_bytes (access_ti s (update_ti s bs v) xbs) = (from_bytes bs::'b)"
    by (simp add: match xmem_type_class.eq_upto_padding_from_bytes_eq)
  moreover have "update_ti (typ_info_t TYPE('b)) bs vf = from_bytes bs"
    using lbs
    by (metis (mono_tags, lifting) c_type_class.typ_uinfo_size export_size_of export_uinfo_size match
        update_ti_s_from_bytes update_ti_update_ti_t)
  ultimately show ?thesis by simp
qed

lemma xmem_type_field_lookup_update_ti_super_update_bs_conv:
  fixes v::'a
  assumes lbs: "length bs = size_td s"
  assumes lxbs: "length xbs = size_of TYPE('a)"
  shows "update_ti s bs v =
           update_ti (typ_info_t TYPE('a)) (super_update_bs bs (access_ti (typ_info_t TYPE('a)) v xbs) n) v"
  using field_lookup_update_ti_super_update_bs_conv(1) [where m=0, simplified, OF fl lbs lxbs [simplified size_of_def], where v=v]
  by simp


lemma heap_update_list_field_to_root:
  fixes p::"'a ptr"
  assumes cgrd: "c_guard p"
  assumes lbs: "length bs = size_td s"
  shows "heap_update_list (&(p\<rightarrow>f)) bs hp =
         heap_update_list (ptr_val p) (super_update_bs bs (heap_list hp (size_of TYPE('a)) (ptr_val p)) n) hp"
proof -
  from fl
  have off: "word_of_nat (field_offset TYPE('a) f) = word_of_nat n"
    by (simp)
  from c_guard_no_wrap' [OF cgrd]
  have no_overflow: "unat (ptr_val p) + size_of TYPE('a) \<le> addr_card" .
  from lbs fl have n_bound: "n + length bs \<le> size_of TYPE('a)"
    by (metis add.commute field_lookup_offset_size size_of_def)

  show ?thesis
    apply (simp add: field_lvalue_def off )
    apply (rule heap_update_list_super_update_bs_heap_list [OF no_overflow n_bound])
    done
qed


lemma heap_list_field_to_root:
  fixes p::"'a ptr"
  shows "heap_list hp (size_td s) &(p\<rightarrow>f) =
          take (size_td s) ((drop n) (heap_list hp (size_of TYPE('a)) (ptr_val (p::'a ptr))))"
proof -
  from fl have off: "(field_offset TYPE('a) f) = n" by simp
  from fl
  have n_bound: "n \<le> size_of TYPE('a)"
    by (meson n_t nat_less_le)
  from fl
  have s_bound: "size_td s \<le> size_of TYPE('a) - n"
    by (metis field_lookup_offset_size nat_move_sub_le size_of_def)

  show ?thesis
    by (simp add: field_lvalue_def off drop_heap_list_le [OF n_bound] take_heap_list_le [OF s_bound])
qed


lemma heap_list_field_super_update_bs_root_conv:
  fixes p::"'a ptr"
  shows "super_update_bs (heap_list hp (size_td s) (&(p\<rightarrow>f))) (heap_list hp (size_of TYPE('a)) (ptr_val p)) n =
         (heap_list hp (size_of TYPE('a)) (ptr_val p))"
proof -

  have l: "length (heap_list hp (size_of TYPE('a)) (ptr_val p)) = size_of TYPE('a)"
    by simp

  from l fl have l_take: "(length (take n (heap_list hp (size_of TYPE('a)) (ptr_val p)))) = n"
    by (simp add: le_less n_t)

  from l fl n_t
  have l_s_take: "length ((take (size_td s) (drop n (heap_list hp (size_of TYPE('a)) (ptr_val p))))) = size_td s"
    by (metis heap_list_field_to_root heap_list_length)

  have com: "(n + size_td s) = (size_td s + n)"
    by simp
  show ?thesis
    apply (simp add: super_update_bs_def)
    apply (subst heap_list_field_to_root)
    apply (rule  append_take_dropI)
     apply (simp only: l_take)
    apply (rule  append_take_dropI)
     apply (simp only: l_s_take l_take)
    apply (simp only: l_s_take l_take)
    apply (simp)
    apply (subst com)
    apply (rule refl)
    done

qed

lemma heap_update_field_root_conv:
  fixes p::"'a ptr"
  assumes cgrd: "c_guard p"
  shows "heap_update (PTR('b) &(p\<rightarrow>f)) v hp =
         heap_update p (update_ti s (to_bytes v (heap_list hp (size_of TYPE('b)) (&(p\<rightarrow>f)))) (h_val hp p)) hp"
unfolding heap_update_def c_type_class.heap_update_def ptr_val_def
proof -
  show "heap_update_list &(p\<rightarrow>f) (to_bytes v (heap_list hp (size_of TYPE('b)) &(p\<rightarrow>f))) hp =
    heap_update_list (ptr_val p)
     (to_bytes
       (update_ti s (to_bytes v (heap_list hp (size_of TYPE('b)) &(p\<rightarrow>f))) (h_val hp p))
       (heap_list hp (size_of TYPE('a)) (ptr_val p)))
     hp" (is "?lhs = ?rhs")
  proof -
    define bs where "bs = to_bytes v (heap_list hp (size_of TYPE('b)) (&(p\<rightarrow>f)))"
    have lbs: "length bs = size_td s"
      unfolding bs_def
      by (simp add: export_size_of match)

    from heap_update_list_field_to_root [OF cgrd lbs]
    have eq1:
      "heap_update_list (&(p\<rightarrow>f)) bs hp =
          heap_update_list (ptr_val p) (super_update_bs bs (heap_list hp (size_of TYPE('a)) (ptr_val p)) n) hp"
      by simp


    have lhl: "length (heap_list hp (size_of TYPE('a)) (ptr_val p)) = size_of TYPE('a)"
      by simp
    from xmem_type_field_lookup_update_ti_super_update_bs_conv [OF lbs this, where v="h_val hp p"]
    have eq2:
      "update_ti s bs (h_val hp p) =
          update_ti (typ_info_t TYPE('a))
            (super_update_bs bs
              (access_ti (typ_info_t TYPE('a)) (h_val hp p) (heap_list hp (size_of TYPE('a)) (ptr_val p)))
              n)
            (h_val hp p)" .

    have eq3: "access_ti (typ_info_t TYPE('a)) (h_val hp p) (heap_list hp (size_of TYPE('a)) (ptr_val p)) =
                 heap_list hp (size_of TYPE('a)) (ptr_val p)"
      apply (simp add: h_val_def from_bytes_def update_ti_t_def size_of_def)
      using lhl
      by (metis local.field_sz_size_of local.field_sz_size_td local.lense.access_result_size
          local.lense.eq_padding_neq_is_value_byte local.lense.field_access_eq_padding1
          local.lense.is_value_byte_acc_upd_cancel nth_equalityI)

    have lsuper: "length (super_update_bs bs (heap_list hp (size_of TYPE('a)) (ptr_val p)) n) = size_of TYPE('a)"
      using flense.eq_padding_refl lbs lhl padding_base.eq_padding_length1
        xmem_type_field_lookup_lense_eq_padding_super_update_bs by blast

    thm field_lookup_eq_padding_super_update_bs
    have eq_padding_bs: "eq_padding (export_uinfo s) bs (heap_list hp (size_td s) (&(p\<rightarrow>f)))"
      apply (simp add: bs_def to_bytes_def c_type_class.to_bytes_def)
      by (metis (mono_tags, lifting) c_type_class.to_bytes_def export_size_of heap_list_length match
          xmem_type_class.eq_padding_to_bytes)

    have l_take_drop: "length (take (size_td s) (drop n (heap_list hp (size_of TYPE('a)) (ptr_val p)))) = size_td s"
      by (metis heap_list_field_to_root heap_list_length)
    thm heap_list_field_super_update_bs_root_conv


    from xmem_type_field_lookup_eq_padding_super_update_bs [OF lhl lbs,
            where bs' = "take (size_td s) (drop n (heap_list hp (size_of TYPE('a)) (ptr_val p)))", OF l_take_drop,
            simplified heap_list_field_to_root [symmetric], simplified heap_list_field_super_update_bs_root_conv]
         eq_padding_bs
    have "eq_padding (typ_uinfo_t TYPE('a)) (super_update_bs bs (heap_list hp (size_of TYPE('a)) (ptr_val p)) n)
            (heap_list hp (size_of TYPE('a)) (ptr_val p))"
     by (simp )

    hence eq_padding: "lense.eq_padding (super_update_bs bs (heap_list hp (size_of TYPE('a)) (ptr_val p)) n)
            (heap_list hp (size_of TYPE('a)) (ptr_val p))"
     by (simp add:  eq_padding_lense_conv)

    from eq_padding
    have eq4:
      "(to_bytes
          (update_ti (typ_info_t TYPE('a))
            (super_update_bs bs (heap_list hp (size_of TYPE('a)) (ptr_val p)) n) (h_val hp p))
          (heap_list hp (size_of TYPE('a)) (ptr_val p))) =
       (super_update_bs bs (heap_list hp (size_of TYPE('a)) (ptr_val p)) n)"
      apply (simp add: to_bytes_def)
      by (smt (verit) lhl local.lense.access_result_size local.lense.eq_padding_neq_is_value_byte
          local.lense.field_access_eq_padding1 local.lense.is_value_byte_acc_upd_cancel lsuper nth_equalityI)

    show ?thesis
      unfolding bs_def [symmetric]
      apply (simp add: eq1)
      apply (simp add: eq2)
      apply (simp add: eq3)
      apply (simp add: eq4)
      done
  qed
qed

lemma heap_update_padding_field_root_conv:
  fixes p::"'a ptr"
  assumes cgrd: "c_guard p"
  assumes lbs: "length bs = size_of TYPE ('b)"
  shows "heap_update_padding (PTR('b) &(p\<rightarrow>f)) v bs hp =
         heap_update_padding p (update_ti s (to_bytes v bs) (h_val hp p))
          (super_update_bs bs (heap_list hp (size_of TYPE('a)) (ptr_val p)) n) hp"
unfolding heap_update_padding_def c_type_class.heap_update_padding_def ptr_val_def
proof -
  show "heap_update_list &(p\<rightarrow>f) (to_bytes v bs) hp =
    heap_update_list (ptr_val p)
     (to_bytes
       (update_ti s (to_bytes v bs) (h_val hp p))
       (super_update_bs bs (heap_list hp (size_of TYPE('a)) (ptr_val p)) n))
     hp" (is "?lhs = ?rhs")
  proof -
    define bs' where "bs' = to_bytes v bs"
    have lbs': "length bs' = size_td s"
      unfolding bs'_def
      by (simp add: export_size_of lbs match)


    from heap_update_list_field_to_root [OF cgrd lbs']
    have eq1:
      "heap_update_list (&(p\<rightarrow>f)) bs' hp =
          heap_update_list (ptr_val p) (super_update_bs bs' (heap_list hp (size_of TYPE('a)) (ptr_val p)) n) hp"
      by simp


    have lhl: "length (heap_list hp (size_of TYPE('a)) (ptr_val p)) = size_of TYPE('a)"
      by simp
    from xmem_type_field_lookup_update_ti_super_update_bs_conv [OF lbs' this, where v="h_val hp p"]
    have eq2:
      "update_ti s bs' (h_val hp p) =
          update_ti (typ_info_t TYPE('a))
            (super_update_bs bs'
              (access_ti (typ_info_t TYPE('a)) (h_val hp p) (heap_list hp (size_of TYPE('a)) (ptr_val p)))
              n)
            (h_val hp p)" .

    have eq3: "access_ti (typ_info_t TYPE('a)) (h_val hp p) (heap_list hp (size_of TYPE('a)) (ptr_val p)) =
                 heap_list hp (size_of TYPE('a)) (ptr_val p)"
      apply (simp add: h_val_def from_bytes_def update_ti_t_def size_of_def)
      using lhl
      by (metis local.field_sz_size_of local.field_sz_size_td local.lense.access_result_size
          local.lense.eq_padding_neq_is_value_byte local.lense.field_access_eq_padding1
          local.lense.is_value_byte_acc_upd_cancel nth_equalityI)

    have lsuper: "length (super_update_bs bs' (heap_list hp (size_of TYPE('a)) (ptr_val p)) n) = size_of TYPE('a)"
      using flense.eq_padding_refl lbs' lhl padding_base.eq_padding_length1
        xmem_type_field_lookup_lense_eq_padding_super_update_bs by blast

    thm field_lookup_eq_padding_super_update_bs

    have l_take_drop: "length (take (size_td s) (drop n (heap_list hp (size_of TYPE('a)) (ptr_val p)))) = size_td s"
      by (metis heap_list_field_to_root heap_list_length)
    have eq4:
      "(to_bytes
         (update_ti (typ_info_t TYPE('a))
           (super_update_bs bs' (heap_list hp (size_of TYPE('a)) (ptr_val p)) n) (h_val hp p))
         (super_update_bs bs (heap_list hp (size_of TYPE('a)) (ptr_val p)) n)) =
       (super_update_bs bs' (heap_list hp (size_of TYPE('a)) (ptr_val p)) n)"
      apply (simp add: to_bytes_def)
      by (smt (verit, ccfv_threshold) bs'_def export_size_of field_lookup_lense_eq_padding_fieldtyp_conv
          lbs lhl local.lense.access_result_size local.lense.complement local.lense.eq_padding_acc local.lense.is_padding_byte_def local.lense.is_value_byte_def lsuper match mem_type_class.mem_type_simps(2) nth_equalityI wf_type_class.len xmem_type_class.lense_eq_padding_to_bytes xmem_type_field_lookup_lense_eq_padding_super_update_bs)

    show ?thesis
      unfolding bs'_def [symmetric]
      apply (simp add: eq1)
      apply (simp add: eq2)
      apply (simp add: eq3)
      apply (simp add: eq4)
      done
  qed
qed

lemma heap_update_field_root_conv':
  fixes p::"'a ptr"
  assumes cgrd: "c_guard p"
  shows "heap_update (PTR('b) &(p\<rightarrow>f)) v hp =
         heap_update p (update_ti s (to_bytes_p v) (h_val hp p)) hp"
proof -
  have "eq_upto_padding (export_uinfo s) (to_bytes_p v) (to_bytes v (heap_list hp (size_of TYPE('b)) (&(p\<rightarrow>f))))"
    apply (simp add: to_bytes_def c_type_class.to_bytes_def to_bytes_p_def c_type_class.to_bytes_p_def)
    by (simp add: field_lookup_eq_upto_padding_lense_conv field_lookup_lense_eq_upto_padding_fieldtyp_conv
        xmem_type_class.lense.field_access_eq_upto_padding)
  hence "update_ti s (to_bytes_p v) (h_val hp p) =
          update_ti s (to_bytes v (heap_list hp (size_of TYPE('b)) (&(p\<rightarrow>f)))) (h_val hp p)"
    by (simp add: field_lookup_eq_upto_padding_lense_conv padding_base.eq_upto_padding_def)
  with heap_update_field_root_conv [OF cgrd] show ?thesis by simp
qed


lemma heap_update_padding_field_root_conv':
  fixes p::"'a ptr"
  assumes cgrd: "c_guard p"
  assumes lbs: "length bs = size_of TYPE ('b)"
  shows "heap_update_padding (PTR('b) &(p\<rightarrow>f)) v bs hp =
         heap_update_padding p (update_ti s (to_bytes_p v) (h_val hp p))
           (super_update_bs bs (heap_list hp (size_of TYPE('a)) (ptr_val p)) n) hp"
  proof -
  have "eq_upto_padding (export_uinfo s) (to_bytes_p v) (to_bytes v bs)"
    apply (simp add: to_bytes_def c_type_class.to_bytes_def to_bytes_p_def c_type_class.to_bytes_p_def)
    by (simp add: field_lookup_eq_upto_padding_lense_conv field_lookup_lense_eq_upto_padding_fieldtyp_conv
        xmem_type_class.lense.field_access_eq_upto_padding)
  hence "update_ti s (to_bytes_p v) (h_val hp p) =
          update_ti s (to_bytes v bs) (h_val hp p)"
    by (simp add: field_lookup_eq_upto_padding_lense_conv padding_base.eq_upto_padding_def)
  with heap_update_padding_field_root_conv [OF cgrd lbs] show ?thesis by simp
qed

end
end


lemma heap_update_field_root_conv'':
  fixes p::"'a ptr"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (adjust_ti (typ_info_t TYPE('b::xmem_type)) fld (fld_update \<circ> (\<lambda>x _. x)), n)"
  assumes fg_cons: "fg_cons fld (fld_update \<circ> (\<lambda>x _. x))"
  assumes cgrd: "c_guard p"
  shows "heap_update (PTR('b) &(p\<rightarrow>f)) v hp =
         heap_update p (fld_update (\<lambda>_. v) (h_val hp p)) hp"
proof -
  have match: "export_uinfo (adjust_ti (typ_info_t TYPE('b)) fld (fld_update \<circ> (\<lambda>x _. x))) = typ_uinfo_t TYPE('b)"
    apply (subst c_type_class.typ_uinfo_t_def)
    apply (rule export_tag_adjust_ti(1) )
    apply (rule fg_cons)
    apply (simp)
    done
  from field_desc_adjust_ti(1) [rule_format, OF fg_cons, of "(typ_info_t TYPE('b))"]
  have upd_eq:
    "update_ti_t (adjust_ti (typ_info_t TYPE('b)) fld (fld_update \<circ> (\<lambda>x _. x))) bs v =
         fld_update (\<lambda>_. update_ti_t (typ_info_t TYPE('b)) bs (fld v)) v " for bs v
    by (simp add: update_desc_def)
  from this [of "(to_bytes_p v)" "h_val hp p"]
  have val_conv:
    "(update_ti (adjust_ti (typ_info_t TYPE('b)) fld (fld_update \<circ> (\<lambda>x _. x))) (to_bytes_p v) (h_val hp p))  =
          (fld_update (\<lambda>_. v) (h_val hp p))"
    apply (simp add: update_ti_t_def size_of_def c_type_class.size_of_def)
    by (metis (mono_tags, opaque_lifting) inv_p length_to_bytes_p update_ti_s_from_bytes update_ti_t_def)

  note heap_conv = heap_update_field_root_conv' [OF fl match cgrd, of v hp]
  show ?thesis
    apply (simp add: heap_conv)
    apply (simp add: val_conv)
    done
qed

lemma heap_update_field_root_conv_pointless':
  fixes p::"'a ptr"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (adjust_ti (typ_info_t TYPE('b::xmem_type)) fld (fld_update \<circ> (\<lambda>x _. x)), n)"
  assumes fg_cons: "fg_cons fld (fld_update \<circ> (\<lambda>x _. x))"
  assumes cgrd: "c_guard p"
  shows "heap_update (PTR('b) &(p\<rightarrow>f)) v = 
         (\<lambda>hp. heap_update p (fld_update (\<lambda>_. v) (h_val hp p)) hp)"
  using heap_update_field_root_conv'' [OF fl fg_cons cgrd]
  by (simp add: fun_eq_iff)

lemma heap_update_padding_field_root_conv'':
  fixes p::"'a ptr"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (adjust_ti (typ_info_t TYPE('b::xmem_type)) fld (fld_update \<circ> (\<lambda>x _. x)), n)"
  assumes fg_cons: "fg_cons fld (fld_update \<circ> (\<lambda>x _. x))"
  assumes cgrd: "c_guard p"
  assumes lbs: "length bs = size_of TYPE ('b)"
  shows "heap_update_padding (PTR('b) &(p\<rightarrow>f)) v bs hp =
         heap_update_padding p (fld_update (\<lambda>_. v) (h_val hp p))
           (super_update_bs bs (heap_list hp (size_of TYPE('a)) (ptr_val p)) n) hp"
proof -
  have match: "export_uinfo (adjust_ti (typ_info_t TYPE('b)) fld (fld_update \<circ> (\<lambda>x _. x))) = typ_uinfo_t TYPE('b)"
    apply (subst c_type_class.typ_uinfo_t_def)
    apply (rule export_tag_adjust_ti(1) )
    apply (rule fg_cons)
    apply (simp)
    done
  from field_desc_adjust_ti(1) [rule_format, OF fg_cons, of "(typ_info_t TYPE('b))"]
  have upd_eq:
    "update_ti_t (adjust_ti (typ_info_t TYPE('b)) fld (fld_update \<circ> (\<lambda>x _. x))) bs v =
         fld_update (\<lambda>_. update_ti_t (typ_info_t TYPE('b)) bs (fld v)) v " for bs v
    by (simp add: update_desc_def)
  from this [of "(to_bytes_p v)" "h_val hp p"]
  have val_conv:
    "(update_ti (adjust_ti (typ_info_t TYPE('b)) fld (fld_update \<circ> (\<lambda>x _. x))) (to_bytes_p v) (h_val hp p))  =
          (fld_update (\<lambda>_. v) (h_val hp p))"
    apply (simp add: update_ti_t_def size_of_def c_type_class.size_of_def)
    by (metis (mono_tags, opaque_lifting) inv_p length_to_bytes_p update_ti_s_from_bytes update_ti_t_def)

  note heap_conv = heap_update_padding_field_root_conv' [OF fl match cgrd lbs, of v hp]
  show ?thesis
    apply (simp add: heap_conv)
    apply (simp add: val_conv)
    done
qed


lemma heap_update_field_root_conv''':
  fixes p::"'a ptr"
  assumes fl: "field_ti TYPE('a) f = Some s"
  assumes cgrd: "c_guard p"
  assumes match: "export_uinfo s = typ_uinfo_t TYPE('b::xmem_type)"
  shows "heap_update (PTR('b) &(p\<rightarrow>f)) v hp =
         heap_update p (update_ti s (to_bytes_p v) (h_val hp p)) hp"
proof -
  from fl obtain n where fl': "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
    by (auto simp add: field_ti_def split: option.splits)

  from heap_update_field_root_conv' [OF fl' match cgrd, of v hp]
  show ?thesis
    by (simp)
qed

lemma heap_update_padding_field_root_conv''':
  fixes p::"'a ptr"
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
  assumes cgrd: "c_guard p"
  assumes match: "export_uinfo s = typ_uinfo_t TYPE('b::xmem_type)"
  assumes lbs: "length bs = size_of TYPE ('b)"
  shows "heap_update_padding (PTR('b) &(p\<rightarrow>f)) v bs hp =
         heap_update_padding p (update_ti s (to_bytes_p v) (h_val hp p))
          (super_update_bs bs (heap_list hp (size_of TYPE('a)) (ptr_val p)) n) hp"
proof -
  from heap_update_padding_field_root_conv' [OF fl match cgrd lbs, of v hp]
  show ?thesis
    by (simp)
qed

end


lemma length_array_to_bytes:
  fixes arr::"('a::array_outer_max_size['b::array_max_count])"
  shows "length (to_bytes arr (heap_list h (CARD('b) * size_of TYPE('a)) (ptr_val p))) =
         size_of TYPE('a) * CARD('b)"
  by (simp add: lense.access_result_size)

lemma take_drop_append_first: "m + n \<le> length xs \<Longrightarrow>  take n (drop m (xs @ ys)) = take n (drop m xs)"
  by simp

lemma size_td_list_array:
"size_td_list
     (map (\<lambda>n. DTuple
                 (adjust_ti (typ_info_t TYPE('a::xmem_type)) (\<lambda>x. x.[n])
                   (\<lambda>x f. Arrays.update f n x))
                 (replicate n CHR ''1'')
                 \<lparr>field_access = xto_bytes \<circ> (\<lambda>x. x.[n]),
                    field_update = (\<lambda>x f. Arrays.update f n x) \<circ> xfrom_bytes,
                    field_sz = size_of TYPE('a)\<rparr>)
       [0..<n]) = n * size_of TYPE('a) "
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (simp add: size_of_def)
qed

lemma length_access_ti_list_array:
  fixes arr::"('a::array_outer_max_size['b::array_max_count])"
  assumes lxbs: "length xbs = n * size_of TYPE('a)"
  shows
 "length (access_ti_list
         (map (\<lambda>n. DTuple
                     (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. x.[n])
                       (\<lambda>x f. Arrays.update f n x))
                     (replicate n CHR ''1'')
                     \<lparr>field_access = xto_bytes \<circ> (\<lambda>x. x.[n]),
                        field_update = (\<lambda>x f. Arrays.update f n x) \<circ> xfrom_bytes,
                        field_sz = size_of TYPE('a)\<rparr>)
           [0..<n])
         arr xbs) = n * size_of TYPE('a)"
  using lxbs
proof (induct n arbitrary: xbs)
  case 0
  then show ?case by simp
next
  case (Suc n)

  have lxbs': "length xbs =
    size_td_list
     (map (\<lambda>n. DTuple
                 (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. x.[n])
                   (\<lambda>x f. Arrays.update f n x))
                 (replicate n CHR ''1'')
                 \<lparr>field_access = \<lambda>a. xto_bytes (a.[n]),
                    field_update = \<lambda>a b. Arrays.update b n (xfrom_bytes a),
                    field_sz = size_td (typ_info_t TYPE('a))\<rparr>)
       [0..<n] @
      [DTuple (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. x.[n]) (\<lambda>x f. Arrays.update f n x))
        (replicate n CHR ''1'')
        \<lparr>field_access = \<lambda>a. xto_bytes (a.[n]),
           field_update = \<lambda>a b. Arrays.update b n (xfrom_bytes a),
           field_sz = size_td (typ_info_t TYPE('a))\<rparr>])"
    apply simp
    apply (subst size_td_list_array [simplified size_of_def comp_def])
    using Suc.prems
    apply (simp add: size_of_def)
    done

  from Suc.prems
  have ltake: "length (take (n * size_td (typ_info_t TYPE('a))) xbs) =
                  n * size_td (typ_info_t TYPE('a))"
    by (auto simp add: size_of_def)

  have llast: "length
     (access_ti (typ_info_t TYPE('a)) (arr.[n])
       (take (size_td (typ_info_t TYPE('a)))
         (drop
           (size_td_list
             (map (\<lambda>n. DTuple
                         (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. x.[n])
                           (\<lambda>x f. Arrays.update f n x))
                         (replicate n CHR ''1'')
                         \<lparr>field_access = \<lambda>a. xto_bytes (a.[n]),
                            field_update = \<lambda>a b. Arrays.update b n (xfrom_bytes a),
                            field_sz = size_td (typ_info_t TYPE('a))\<rparr>)
               [0..<n]))
           xbs))) =
    size_td (typ_info_t TYPE('a))"
    by (simp add: lense.access_result_size size_of_def)

  show ?case apply (simp add: size_of_def)
    apply (subst access_ti_append [OF lxbs'])
    apply (subst size_td_list_array [simplified size_of_def comp_def])
    apply simp
    apply (subst Suc.hyps [simplified size_of_def comp_def, OF ltake])
    apply (simp add: llast)
    done
qed

lemma take_drop_take: "m + k \<le> n \<Longrightarrow> n \<le> length xbs \<Longrightarrow> take m (drop k (take n xbs)) = take m (drop k xbs)"
proof (induct xbs arbitrary: m k n)
  case Nil
  then show ?case by simp
next
  case (Cons x xbs)
  then show ?case by (simp add: take_drop)
qed

lemma access_ti_array_index:
  fixes arr::"('a::array_outer_max_size['b::array_max_count])"
  assumes bound: "i < n"
  assumes lxbs: "length xbs = n * size_of TYPE('a)"
  assumes bs: "bs = take (size_of TYPE('a)) (drop (i * (size_of TYPE('a))) xbs)"
  shows
    "access_ti (typ_info_t TYPE('a)) (arr.[i])
       (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) xbs)) =
     take (size_of TYPE('a))
       (drop (i * size_of TYPE('a)) (access_ti (array_tag_n n) arr xbs))"
  using bound lxbs bs
proof (induct n arbitrary: i xbs bs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from Suc.prems obtain
    i_bound: "i < Suc n" and
    lxbs: "length xbs = size_of TYPE('a) + n * size_of TYPE('a)" and
    bs: "bs = take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) xbs)"
    by clarsimp


  show ?case
  proof (cases "i = n")
    case True
    show ?thesis
      apply (simp add: array_tag_n_eq)
      apply (subst access_ti_append)
      apply (simp add: size_td_list_array)
       apply (simp add: size_of_def lxbs)
      apply (subst drop_append_miracle)
       apply (subst length_access_ti_list_array)
        apply (subst size_td_list_array)
      using lxbs
        apply (simp add: True)
       apply (simp add: True)
      apply (simp add: True size_td_list_array)
      apply (simp add: size_of_def)
      by (simp add: lense.access_result_size size_of_def)
  next
    case False
    from False i_bound have i_bound': "i < n" by simp
    from lxbs have lxbs': "length (take (n * size_of TYPE('a)) xbs) = n * size_of TYPE('a)" by simp
    from bs i_bound' lxbs' lxbs False
    have bs':
      "bs = take (size_of TYPE('a))
             (drop (i * size_of TYPE('a)) (take (n * size_of TYPE('a)) xbs))"

      apply (simp)
      apply (subst take_drop_take)
      using less_le_mult_nat sz_nzero apply blast
       apply simp
      apply simp
      done
    show ?thesis
      apply (simp add: array_tag_n_eq)
      apply (subst access_ti_append)
      apply (simp add: size_td_list_array)
       apply (simp add: size_of_def lxbs)
      apply (subst take_drop_append_first)
       apply (subst length_access_ti_list_array)
        apply (subst size_td_list_array)
      using lxbs apply (simp add: )
      using lxbs i_bound False
       apply (metis add.commute less_le_mult_nat mem_type_simps(3) not_less_less_Suc_eq)
      apply (subst size_td_list_array)
      apply (simp add: bs [symmetric])

      using Suc.hyps [where xbs="(take (n * size_of TYPE('a)) xbs)", OF i_bound' lxbs' bs', simplified bs'[symmetric]]
      apply (simp)
      apply (subst array_tag_n_eq)
      apply simp
      done
  qed
qed



lemma access_ti_array_index':
  fixes arr::"('a::array_outer_max_size['b::array_max_count])"
  assumes bound: "i < CARD('b)"
  assumes lbs: "length xbs = (CARD('b) * size_of TYPE('a))"
  assumes bs: "bs = take (size_of TYPE('a)) (drop (i * (size_of TYPE('a))) xbs)"
  shows
   "access_ti (typ_info_t TYPE('a)) (arr.[i]) bs =
    take (size_of TYPE('a))
      (drop (i * size_of TYPE('a))
        (access_ti (typ_info_t TYPE('a['b])) arr xbs))"
  apply (simp add: typ_info_array array_tag_def)
  using access_ti_array_index [OF bound lbs bs, where arr=arr, simplified bs [symmetric]]
  apply simp
  done

lemma fold_index_shift:  "fold f [n..<n + m] = fold (\<lambda>i. f (n + i)) [0..<m]"
proof (induct m arbitrary: n)
  case 0
  then show ?case by simp
next
  case (Suc m)
  thus ?case by simp
qed

lemma fold_Suc_index_shift: "fold f [1..<Suc n] = fold (\<lambda>i. f (Suc i)) [0..<n]"
  using fold_index_shift [where n=1 and m=n and f = f]
  by simp

lemma sum_list_index_shift: "sum_list (map f [n..<n+m]) = sum_list (map (\<lambda>i. f (n + i)) [0..<m])"
  apply (induct m)
   apply auto
  done

lemma sum_list_Suc_index_shift: "sum_list (map f [1..<Suc n]) = sum_list (map (\<lambda>i. f (Suc i)) [0..<n])"
  using sum_list_index_shift [where n=1 and m=n and f = f]
  by simp

lemma upt_Suc_snoc: "[0..<Suc n] = [0..<n] @ [n]"
  by (induct n) auto


lemma sum_list_le_prefix:
  fixes sz:: "nat \<Rightarrow> nat"
  assumes lower: "n \<le> m"
  assumes le: "m \<le> k"
  shows  "sum_list (map sz [n..<m]) \<le> sum_list (map sz [n..<k])"
  apply (subst upt_add_eq_append' [OF lower le])
  apply simp
  done

lemma intvl_off_disj':
  fixes x :: addr
  assumes ylt: "y \<le> off"
  and    zoff: "unat x + off + z \<le> addr_card"
shows   "{x ..+ y} \<inter> {x + of_nat off ..+ z} = {}"
proof (cases "unat x + off + z = addr_card")
  case True
  then show ?thesis
    using ylt zoff
    apply (simp add: intvl_def)
    apply (safe, clarsimp)
  proof -
    fix k :: nat and ka :: nat
    assume a1: "unat x + off + z = addr_card"
    assume a2: "y \<le> off"
    assume a3: "k < y"
    assume a4: "(word_of_nat k::addr_bitsize word) = word_of_nat off + word_of_nat ka"
    assume "ka < z"
    then have "ka + off < addr_card"
      using a1 by linarith
    then show False
      using a4 a3 a2 by (metis (no_types) add.commute add_lessD1 len_of_addr_card less_le_trans nat_less_le unat_of_nat_eq word_arith_nat_add)
  qed
next
  case False
  with zoff have le: "off + z < addr_card" by simp
  show ?thesis
    apply (rule intvl_off_disj [OF ylt])
    using le by (simp add: addr_card_wb)
qed

lemma heap_update_list_padding_fold_partition:
  fixes   v:: "nat \<Rightarrow> byte list \<Rightarrow> byte list"
    and  sz:: "nat \<Rightarrow> nat"
    and off:: "nat \<Rightarrow> nat"
  assumes no_overflow: "unat a + length bs \<le> addr_card"
  assumes partition: "bs = concat (map (\<lambda>i. take (sz i) (drop (off i) bs)) [0..<m])"
  assumes lbs: "length bs = sum_list (map sz [0..<m])"
  assumes partition_pbs: "pbs = concat (map (\<lambda>i. take (sz i) (drop (off i) pbs)) [0..<m])"
  assumes lpbs: "length pbs = sum_list (map sz [0..<m])"
  assumes off_sz: "\<And>i. i < m \<Longrightarrow> off i = sum_list (map sz [0..<i])"
  assumes val: "\<And>i. i < m \<Longrightarrow>
                  v i (take (sz i) (drop (off i) pbs)) =
                    (take (sz i) (drop (off i) bs))"
  shows
   "heap_update_list a bs h =
      fold (\<lambda>i h. heap_update_list
                    (a + word_of_nat (off i))
                    (v i (take (sz i) (drop (off i) pbs)))
                    h)
         [0..<m] h"
  using no_overflow partition lbs partition_pbs lpbs off_sz val
 proof (induct m arbitrary: a bs pbs h )
  case 0
  then show ?case by simp
next
  case (Suc m)
  from Suc.prems obtain
    no_overflow: "unat a + length bs \<le> addr_card" and
    bs_partition:  "bs = concat (map (\<lambda>i. take (sz i) (drop (off i) bs)) [0..<Suc m])" and
    pbs_partition:  "pbs = concat (map (\<lambda>i. take (sz i) (drop (off i) pbs)) [0..<Suc m])" and
    lbs: "length bs = sum_list (map sz [0..<Suc m])" and
    lpbs: "length pbs = sum_list (map sz [0..<Suc m])" and
    off_sz: "\<And>i. i < Suc m \<Longrightarrow> off i = sum_list (map sz [0..<i])" and
    val: "\<And>i. i < Suc m \<Longrightarrow>
              v i (take (sz i) (drop (off i) pbs)) =
              take (sz i) (drop (off i) bs)"
    by clarsimp
  have unroll: "[0..<Suc m] = [0..<m] @ [m]"
    by (rule upt_Suc_snoc)

  define bs' where "bs' = concat (map (\<lambda>i. take (sz i) (drop (off i) bs)) [0..<m])"
  define bsm where "bsm = take (sz m) (drop (off m) bs)"

  define pbs' where "pbs' = concat (map (\<lambda>i. take (sz i) (drop (off i) pbs)) [0..<m])"
  define pbsm where "pbsm = take (sz m) (drop (off m) pbs)"

  from bs_partition have bs: "bs = bs' @ bsm"
    unfolding bsm_def bs'_def
    apply (subst (asm) unroll)
    apply simp
    done

  from pbs_partition have pbs: "pbs = pbs' @ pbsm"
    unfolding pbsm_def pbs'_def
    apply (subst (asm) unroll)
    apply simp
    done

  from lbs have lbs1: "length bs = sum_list (map sz [0..<m]) + sz m"
    apply (subst (asm) unroll)
    apply simp
    done

  from lpbs have lpbs1: "length pbs = sum_list (map sz [0..<m]) + sz m"
    apply (subst (asm) unroll)
    apply simp
    done

  have lbsm: "length bsm = sz m"
    apply (simp add: bsm_def)
    using lbs1 off_sz [of m]
    apply simp
    done

  have lpbsm: "length pbsm = sz m"
    apply (simp add: pbsm_def)
    using lpbs1 off_sz [of m]
    apply simp
    done

  from lbsm lbs1 have lbs': "length bs' = sum_list (map sz [0..<m])"
    apply (subst (asm) bs)
    apply simp
    done

  from lpbsm lpbs1 have lpbs': "length pbs' = sum_list (map sz [0..<m])"
    apply (subst (asm) pbs)
    apply simp
    done

  from off_sz have off_sz': "(\<And>i. i < m \<Longrightarrow> off i = sum_list (map sz [0..<i])) " by auto

  {
    fix i
    assume bound: "i < m"
    hence bound': "i < Suc m" by simp
    from val [OF this]
    have v_i: "v i (take (sz i) (drop (off i) pbs)) =
               take (sz i) (drop (off i) bs)" .

    from off_sz [OF bound'] have off_i: "off i = sum_list (map sz [0..<i])".
    from off_sz [of m] have off_m: "off m = sum_list (map sz [0..<m])" by simp

    from bound have "Suc i \<le> m" by simp
    from sum_list_le_prefix [where n=0, OF _ this]
    have *: "sum_list (map sz [0..<Suc i]) \<le> sum_list (map sz [0..<m])" by simp
    then have bound_bs': "off i + sz i \<le> length bs'" using off_i lbs' by simp
    from * have bound_pbs': "off i + sz i \<le> length pbs'" using off_i lpbs' by simp

    have take_eq1: "take (sz i) (drop (off i) bs) = take (sz i) (drop (off i) bs')"
      apply (subst bs)
      apply (subst take_drop_append_first [OF bound_bs'])
      apply simp
      done
    have take_eq2: "take (sz i) (drop (off i) pbs) = take (sz i) (drop (off i) pbs')"
      apply (subst pbs)
      apply (subst take_drop_append_first [OF bound_pbs'])
      apply simp
      done

    from v_i
    have "v i (take (sz i) (drop (off i) pbs')) =
        take (sz i) (drop (off i) bs')"
      by (simp add: take_eq1 take_eq2)
  } note val' = this

  from no_overflow
  have no_overflow': "unat a + length bs' \<le> addr_card "
    by (simp add: bs)
  {
    fix i
    assume bound: "i < m"
    hence bound': "i < Suc m" by simp

    from bound have "Suc i \<le> m" by simp
    from sum_list_le_prefix [where n=0, OF _ this]
    have sum_le: "sum_list (map sz [0..<Suc i]) \<le> sum_list (map sz [0..<m])" by simp
    from off_sz [OF bound'] have off_i: "off i = sum_list (map sz [0..<i])".
    have "take (sz i) (drop (off i) bs) = take (sz i) (drop (off i) bs')"
      apply (subst bs)
      using lbs' sum_le off_i
      apply simp
      done
  } note take_drop_eq = this

  from take_drop_eq
  have map_eq: "map (\<lambda>i. take (sz i) (drop (off i) bs)) [0..<m] =
                map (\<lambda>i. take (sz i) (drop (off i) bs')) [0..<m]"
    by simp

  {
    fix i
    assume bound: "i < m"
    hence bound': "i < Suc m" by simp

    from bound have "Suc i \<le> m" by simp
    from sum_list_le_prefix [where n=0, OF _ this]
    have sum_le: "sum_list (map sz [0..<Suc i]) \<le> sum_list (map sz [0..<m])" by simp
    from off_sz [OF bound'] have off_i: "off i = sum_list (map sz [0..<i])".
    have "take (sz i) (drop (off i) pbs) = take (sz i) (drop (off i) pbs')"
      apply (subst pbs)
      using lpbs' sum_le off_i
      apply simp
      done
  } note take_drop_eq' = this

  from take_drop_eq'
  have map_eq': "map (\<lambda>i. take (sz i) (drop (off i) pbs)) [0..<m] =
                map (\<lambda>i. take (sz i) (drop (off i) pbs')) [0..<m]"
    by simp


  from bs_partition have bs'_partition: "bs' = concat (map (\<lambda>i. take (sz i) (drop (off i) bs')) [0..<m])"
    apply (subst map_eq [symmetric])
    apply (simp add: bs'_def)
    done

  from pbs_partition have pbs'_partition: "pbs' = concat (map (\<lambda>i. take (sz i) (drop (off i) pbs')) [0..<m])"
    apply (subst map_eq' [symmetric])
    apply (simp add: pbs'_def)
    done

  from lbs' off_sz [of m]
  have off_m: "off m = length bs'"
    by simp

  have vm_eq: " (v m (take (sz m) (drop (length bs') pbs') @
                    take (sz m - (length pbs' - length bs')) (drop (length bs' - length pbs') pbsm))) = bsm"
    by (metis bsm_def drop_append length_drop lessI off_m pbs take_append val)


  have fold_pbs':
    "(fold
       (\<lambda>i. heap_update_list (a + word_of_nat (off i)) (v i (take (sz i) (drop (off i) pbs))))
       [0..<m] h) =
     (fold
       (\<lambda>i. heap_update_list (a + word_of_nat (off i)) (v i (take (sz i) (drop (off i) pbs'))))
       [0..<m] h)"
    apply (rule fold_cong)
    using take_drop_eq' by auto

  note hyp = Suc.hyps [where a=a and bs=bs' and pbs=pbs' and h=h, OF no_overflow' bs'_partition lbs' pbs'_partition lpbs' off_sz' val']
  show ?case
    apply (subst unroll)
    apply (subst fold_append)
    apply (simp only: comp_def)
    apply (subst bs)
    apply (subst fold_pbs')
    apply (subst pbs)
    apply (subst heap_update_list_concat_unfold)
    apply (subst hyp [ symmetric])
    apply assumption
    apply (simp add: off_m vm_eq)
    done
qed

lemma heap_update_list_fold_partition:
  fixes   v:: "nat \<Rightarrow> byte list \<Rightarrow> byte list"
    and  sz:: "nat \<Rightarrow> nat"
    and off:: "nat \<Rightarrow> nat"
  assumes no_overflow: "unat a + length bs \<le> addr_card"
  assumes partition: "bs = concat (map (\<lambda>i. take (sz i) (drop (off i) bs)) [0..<m])"
  assumes lbs: "length bs = sum_list (map sz [0..<m])"
  assumes off_sz: "\<And>i. i < m \<Longrightarrow> off i = sum_list (map sz [0..<i])"
  assumes val: "\<And>i. i < m \<Longrightarrow>
                  v i (take (sz i) (drop (off i) (heap_list h (length bs) a))) =
                    (take (sz i) (drop (off i) bs))"
  shows
   "heap_update_list a bs h =
      fold (\<lambda>i h. heap_update_list
                    (a + word_of_nat (off i))
                    (v i ((heap_list h (sz i) (a + word_of_nat (off i)))))
                    h)
         [0..<m] h"
  using no_overflow partition lbs off_sz val
 proof (induct m arbitrary: a bs h )
  case 0
  then show ?case by simp
next
  case (Suc m)
  from Suc.prems obtain
    no_overflow: "unat a + length bs \<le> addr_card" and
    bs_partition:  "bs = concat (map (\<lambda>i. take (sz i) (drop (off i) bs)) [0..<Suc m])" and
    lbs: "length bs = sum_list (map sz [0..<Suc m])" and
    off_sz: "\<And>i. i < Suc m \<Longrightarrow> off i = sum_list (map sz [0..<i])" and
    val: "\<And>i. i < Suc m \<Longrightarrow>
              v i (take (sz i) (drop (off i) (heap_list h (length bs) a))) =
              take (sz i) (drop (off i) bs)"
    by clarsimp
  have unroll: "[0..<Suc m] = [0..<m] @ [m]"
    by (rule upt_Suc_snoc)

  define bs' where "bs' = concat (map (\<lambda>i. take (sz i) (drop (off i) bs)) [0..<m])"
  define bsm where "bsm = take (sz m) (drop (off m) bs)"

  from bs_partition have bs: "bs = bs' @ bsm"
    unfolding bsm_def bs'_def
    apply (subst (asm) unroll)
    apply simp
    done

  from lbs have lbs1: "length bs = sum_list (map sz [0..<m]) + sz m"
    apply (subst (asm) unroll)
    apply simp
    done

  have lbsm: "length bsm = sz m"
    apply (simp add: bsm_def)
    using lbs1 off_sz [of m]
    apply simp
    done

  with lbs1 have lbs': "length bs' = sum_list (map sz [0..<m])"
    apply (subst (asm) bs)
    apply simp
    done

  from off_sz have off_sz': "(\<And>i. i < m \<Longrightarrow> off i = sum_list (map sz [0..<i])) " by auto

  {
    fix i
    assume bound: "i < m"
    hence bound': "i < Suc m" by simp
    from val [OF this]
    have v_i: "v i (take (sz i) (drop (off i) (heap_list h (length bs) a))) =
               take (sz i) (drop (off i) bs)" .

    from off_sz [OF bound'] have off_i: "off i = sum_list (map sz [0..<i])".
    from off_sz [of m] have off_m: "off m = sum_list (map sz [0..<m])" by simp

    from bound have "Suc i \<le> m" by simp
    from sum_list_le_prefix [where n=0, OF _ this]
    have "sum_list (map sz [0..<Suc i]) \<le> sum_list (map sz [0..<m])" by simp
    then have bound_bs': "off i + sz i \<le> length bs'" using off_i lbs' by simp


    have take_eq1: "take (sz i) (drop (off i) bs) = take (sz i) (drop (off i) bs')"
      apply (subst bs)
      apply (subst take_drop_append_first [OF bound_bs'])
      apply simp
      done
    have take_eq2:
      "take (sz i) (drop (off i) (heap_list h (length bs) a)) =
          take (sz i) (drop (off i) (heap_list h (length bs') a))"
      apply (subst lbs1)
      apply (subst lbs')
      apply (subst heap_list_split2)
      using bound_bs' [simplified lbs']
      apply simp
      done
    from v_i
    have "v i (take (sz i) (drop (off i) (heap_list h (length bs') a))) =
        take (sz i) (drop (off i) bs')"
      by (simp add: take_eq1 take_eq2)
  } note val' = this



  from no_overflow
  have no_overflow': "unat a + length bs' \<le> addr_card "
    by (simp add: bs)
  {
    fix i
    assume bound: "i < m"
    hence bound': "i < Suc m" by simp

    from bound have "Suc i \<le> m" by simp
    from sum_list_le_prefix [where n=0, OF _ this]
    have sum_le: "sum_list (map sz [0..<Suc i]) \<le> sum_list (map sz [0..<m])" by simp
    from off_sz [OF bound'] have off_i: "off i = sum_list (map sz [0..<i])".
    have "take (sz i) (drop (off i) bs) = take (sz i) (drop (off i) bs')"
      apply (subst bs)
      using lbs' sum_le off_i
      apply simp
      done
  } note take_drop_eq = this

  from take_drop_eq
  have map_eq: "map (\<lambda>i. take (sz i) (drop (off i) bs)) [0..<m] =
                map (\<lambda>i. take (sz i) (drop (off i) bs')) [0..<m]"
    by simp


  from bs_partition have bs'_partition: "bs' = concat (map (\<lambda>i. take (sz i) (drop (off i) bs')) [0..<m])"
    apply (subst map_eq [symmetric])
    apply (simp add: bs'_def)
    done

  from lbs' off_sz [of m]
  have off_m: "off m = length bs'"
    by simp

  have vm_eq: "v m (heap_list (heap_update_list a bs' h) (sz m) (a + word_of_nat (length bs'))) = bsm"
  proof -
    from val [of m]
    have "v m (take (sz m) (drop (off m) (heap_list h (length bs) a))) = bsm" by (simp add: bsm_def)
    moreover
    have disj: "{a..+length bs'} \<inter> {a + word_of_nat (length bs')..+sz m} = {}"
      apply (simp add: lbs')
      apply (rule intvl_off_disj')
      apply simp
      using no_overflow [simplified lbs1]
      apply (simp)
      done

    have "heap_list (heap_update_list a bs' h) (sz m) (a + word_of_nat (length bs')) =
           take (sz m) (drop (off m) (heap_list h (length bs) a))"
      apply (subst heap_list_update_disjoint_same [OF disj])
      apply (subst lbs1 )
      apply (subst lbs' )
      apply (subst heap_list_take_drop' [OF no_overflow [simplified lbs1]])
       apply (simp add:  off_m [simplified lbs'])
      apply (simp add:  off_m [simplified lbs'])
      done

    ultimately show ?thesis by simp
  qed

  show ?case
    apply (subst unroll)
    apply (subst fold_append)
    apply (simp only: comp_def)
    apply (subst bs)
    apply (subst heap_update_list_concat_unfold)
    apply (subst Suc.hyps [where a=a and bs=bs' and h=h, OF no_overflow' bs'_partition lbs' off_sz' val', symmetric])
    apply assumption
    apply (simp add: off_m vm_eq)
    done
qed

lemma heap_list_map_partition:
  fixes  sz:: "nat \<Rightarrow> nat"
    and off:: "nat \<Rightarrow> nat"
  assumes no_overflow: "unat a + n \<le> addr_card"
  assumes lbs: "n = sum_list (map sz [0..<m])"
  assumes off_sz: "\<And>i. i < m \<Longrightarrow> off i = sum_list (map sz [0..<i])"
  shows
   "heap_list h n a =
      concat (map (\<lambda>i. heap_list h (sz i) (a + word_of_nat (off i))) [0..<m])"
  using no_overflow lbs off_sz
proof (induct m arbitrary: n a)
  case 0
  then show ?case by simp
next
  case (Suc m)
  from Suc.prems obtain
    no_overflow: "unat a + n \<le> addr_card" and
    lbs: "n = sum_list (map sz [0..<Suc m])" and
    off_sz: "\<And>i. i < Suc m \<Longrightarrow> off i = sum_list (map sz [0..<i])"
    by clarsimp
  have unroll: "[0..<Suc m] = [0..<m] @ [m]"
    by (rule upt_Suc_snoc)

  from lbs have lbs1: "n = sum_list (map sz [0..<m]) + sz m"
    apply (subst (asm) unroll)
    apply simp
    done

  from no_overflow lbs1
  have no_overflow': "unat a + (n - sz m) \<le> addr_card"
    by simp
  from lbs1
  have lbs1': "n - sz m = sum_list (map sz [0..<m])"
    by simp
  from lbs1 lbs1'
  have sz_m: "(n - (n - sz m)) = sz m"
    by simp

  from heap_list_split [where k="n - sz m" and n = n and h=h and x=a]
  have split: "heap_list h n a = heap_list h (n - sz m) a @ heap_list h (sz m) (a + word_of_nat (n - sz m))"
    by (simp add: sz_m)

  have hyp: "heap_list h (n - sz m) a = concat (map (\<lambda>i. heap_list h (sz i) (a + word_of_nat (off i))) [0..<m]) "
    apply (rule  Suc.hyps [OF no_overflow' lbs1'])
    using off_sz
    by auto

  from off_sz [of m] lbs1
  have off_m: "(n - sz m) = off m"
    by simp
  show ?case
    apply (subst split)
    apply (subst unroll)
    apply (simp add: hyp )
    apply (simp add: off_m)
    done
qed

lemma array_partition:
assumes lbs: "length bs = m * n"
shows "concat (map (\<lambda>i. take n (drop (i * n) bs)) [0..<m]) = bs"
  using lbs
proof (induct m arbitrary: bs n)
  case 0
  then show ?case by simp
next
  case (Suc m)
  have lbs: "length bs = Suc m * n" by fact
  hence lbs: "length bs = (m * n) + n"
    by simp
  define bs' where "bs' = take (m * n) bs"
  define bs_last where "bs_last = drop (m * n) bs"
  from lbs have bs: "bs = bs' @ bs_last"
    by (simp add: bs'_def bs_last_def)

  from lbs bs
  have lbs': "length bs' = m * n"
    by (metis add_diff_cancel_left' add_diff_cancel_right' bs_last_def eq_concat_lenD length_drop)

  from lbs bs lbs' have lbs_last:  "length bs_last = n"
    by auto

  {
    fix i
    assume bound: "i < m"
    have " take n (drop (i * n) bs) =  take n (drop (i * n) bs')"
      apply (subst bs)
      using lbs' lbs_last bound
      apply simp
      by (metis Suc_leI mult_Suc mult_le_mono order_refl)
  }
  then
  have map_eq: "(map (\<lambda>i. take n (drop (i * n) bs)) [0..<m]) = (map (\<lambda>i. take n (drop (i * n) bs')) [0..<m])"
    by simp

  note hyp = Suc.hyps [OF lbs']
  show ?case
    apply simp
    apply (simp add: map_eq hyp )
    apply (simp add: bs_last_def [symmetric])
    using lbs_last
    apply (simp add: bs)
    done
qed

lemma sum_list_const_fun: "sum_list (map (\<lambda>_. n::nat) [0..<m]) = m * n"
  by (induct m) auto

lemmas export_uinfo_adjust_ti [simp] =  export_tag_adjust_ti(1)[rule_format]


lemma heap_update_list_array:
  fixes arr:: "('a::array_outer_max_size['b::array_max_count])"
  fixes p:: "('a['b]) ptr"
  assumes cgrd: "c_guard p"
  shows
"heap_update_list (ptr_val p) (to_bytes arr (heap_list h (size_of TYPE('a['b])) (ptr_val p))) h =
    fold
      (\<lambda>i h. heap_update_list (ptr_val (array_ptr_index p False i))
               (to_bytes (arr.[i])
                 (heap_list h (size_of TYPE('a)) (ptr_val (array_ptr_index p False i))))
               h)
      [0..<CARD('b)] h"
proof -
  define xbs where
    "xbs= (to_bytes arr (heap_list h (size_of TYPE('a['b])) (ptr_val p)))"
  define sz::"nat \<Rightarrow> nat" where
    "sz = (\<lambda>_. size_of TYPE('a))"
  define off::"nat \<Rightarrow> nat" where
    "off = (\<lambda>i. i * size_of TYPE('a))"
  define v::"nat \<Rightarrow> byte list \<Rightarrow> byte list" where
    "v = (\<lambda>i bs. (to_bytes (arr.[i]) bs))"

  have lxbs: "length xbs = CARD('b) * size_of TYPE('a)"
    by (simp add: xbs_def)

  from c_guard_no_wrap' [OF cgrd] lxbs
  have no_overflow: "unat (ptr_val p) + length xbs \<le> addr_card "
    by simp

  have partition: "xbs = concat (map (\<lambda>i. take (sz i) (drop (off i) xbs)) [0..<CARD('b)]) "
    apply (simp add: sz_def off_def)
    apply (rule array_partition [symmetric, OF lxbs])
    done

  have "sum_list (map sz [0..<CARD('b)]) = CARD('b) * size_of TYPE('a)"
    apply (simp add: sz_def)
    apply (rule sum_list_const_fun)
    done

  with lxbs have lxbs_sum: "length xbs = sum_list (map sz [0..<CARD('b)])" by simp

  have off_sz:  "(\<And>i. i < CARD('b) \<Longrightarrow> off i = sum_list (map sz [0..<i])) "
    unfolding off_def sz_def using sum_list_const_fun
    by auto

  {
    fix i
    assume i_bound: "i < CARD('b)"
    have eq_padding:
      "eq_padding (typ_uinfo_t TYPE('a['b]))
           xbs
           (heap_list h (size_of TYPE('a['b])) (ptr_val p))"
      using eq_padding_to_bytes heap_list_length xbs_def by blast

    from field_lookup_array [OF i_bound, where i=0, simplified]
    have fl: "field_lookup (typ_info_t TYPE('a['b])) [replicate i CHR ''1''] 0 =
            Some (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. x.[i]) (\<lambda>x f. Arrays.update f i x), i * size_of TYPE('a))" .

    have exp:
      "(export_uinfo
            (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x::'a['b]. (x.[i])) (\<lambda>x f. Arrays.update f i x))) =
          typ_uinfo_t TYPE('a)"
      apply (subst export_uinfo_adjust_ti)
        apply (rule fg_cons_array [OF i_bound] )
       apply simp
      apply (simp add: typ_uinfo_t_def)
      done


    from xmem_type_field_lookup_eq_padding_focus [OF fl _ _ eq_padding ]
    have
      "eq_padding (typ_uinfo_t TYPE('a))
           (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) xbs))
           (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) (heap_list h (size_of TYPE('a['b])) (ptr_val p))))"
      using lxbs
      by simp (simp add: exp size_of_def)

    hence eq1:
      "to_bytes (arr.[i]) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) xbs)) =
           to_bytes (arr.[i]) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) (heap_list h (size_of TYPE('a['b])) (ptr_val p))))"
      by (meson eq_padding_to_bytes_eq)
    have "v i (take (sz i) (drop (off i) (heap_list h (length xbs) (ptr_val p)))) =
         take (sz i) (drop (off i) xbs)"
      unfolding v_def lxbs sz_def off_def
      apply (simp add: xbs_def)

      using access_ti_array_index' [OF i_bound lxbs, where arr=arr, OF refl, simplified xbs_def, simplified to_bytes_def [symmetric]]
      apply (simp only: xbs_def [symmetric])
      apply (subst (asm) eq1)
      apply simp
      using eq_padding eq_padding_to_bytes_eq by fastforce
  } note v_padding = this

  {
    fix i
    assume i_bound: "i < CARD('b)"
    have "ptr_val p + word_of_nat i * word_of_nat (size_of TYPE('a))
                =
          ptr_val (PTR_COERCE('a['b] \<rightarrow> 'a) p +\<^sub>p int i)"
      by (simp add: CTypesDefs.ptr_add_def)
  } note deref_conv = this
  note partition = heap_update_list_fold_partition [where a="ptr_val p" and bs=xbs and sz=sz and off=off and v=v
      and h=h and
   m="CARD('b)", OF no_overflow partition lxbs_sum off_sz v_padding, simplified]
  show ?thesis
    apply (simp only: xbs_def [symmetric])
    apply (subst partition)
    apply (rule fold_cong)
      apply simp
     apply simp
    apply (simp add: v_def sz_def off_def array_ptr_index_def deref_conv)
    done
qed

lemma heap_update_array:
  fixes arr:: "('a::array_outer_max_size['b::array_max_count])"
  fixes p:: "('a['b]) ptr"
  assumes cgrd: "c_guard p"
  shows
"heap_update p arr h =
    fold
      (\<lambda>i h. heap_update (array_ptr_index p False i) (arr.[i]) h)
      [0..<CARD('b)] h"
  using heap_update_list_array [OF cgrd]
  by (simp only: heap_update_def)

lemma heap_update_array_pointless:
  fixes arr:: "('a::array_outer_max_size['b::array_max_count])"
  fixes p:: "('a['b]) ptr"
  assumes cgrd: "c_guard p"
  shows
"heap_update p arr =
    fold
      (\<lambda>i h. heap_update (array_ptr_index p False i) (arr.[i]) h)
      [0..<CARD('b)]"
  using heap_update_array [OF cgrd]
  by (simp add: fun_eq_iff)



lemma heap_update_padding_list_array:
  fixes arr:: "('a::array_outer_max_size['b::array_max_count])"
  fixes p:: "('a['b]) ptr"
  assumes cgrd: "c_guard p"
  assumes lbs: "length bs = CARD('b) * size_of TYPE('a)"
  shows
"heap_update_list (ptr_val p) (to_bytes arr bs)  h =
    fold
      (\<lambda>i h. heap_update_list (ptr_val (array_ptr_index p False i))
               (to_bytes (arr.[i])
                 (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs)))
               h)
      [0..<CARD('b)] h"
proof -
  define xbs where
    "xbs= (to_bytes arr bs)"
  define sz::"nat \<Rightarrow> nat" where
    "sz = (\<lambda>_. size_of TYPE('a))"
  define off::"nat \<Rightarrow> nat" where
    "off = (\<lambda>i. i * size_of TYPE('a))"
  define v::"nat \<Rightarrow> byte list \<Rightarrow> byte list" where
    "v = (\<lambda>i bs. (to_bytes (arr.[i]) bs))"
  have lxbs: "length xbs = CARD('b) * size_of TYPE('a)"
    by (simp add: xbs_def lbs)


  from c_guard_no_wrap' [OF cgrd] lxbs
  have no_overflow: "unat (ptr_val p) + length xbs \<le> addr_card "
    by simp

  have partition: "xbs = concat (map (\<lambda>i. take (sz i) (drop (off i) xbs)) [0..<CARD('b)]) "
    apply (simp add: sz_def off_def)
    apply (rule array_partition [symmetric, OF lxbs])
    done

  have partition_bs: "bs = concat (map (\<lambda>i. take (sz i) (drop (off i) bs)) [0..<CARD('b)]) "
    apply (simp add: sz_def off_def)
    apply (rule array_partition [symmetric, OF lbs])
    done

  have *: "sum_list (map sz [0..<CARD('b)]) = CARD('b) * size_of TYPE('a)"
    apply (simp add: sz_def)
    apply (rule sum_list_const_fun)
    done

  with lxbs have lxbs_sum: "length xbs = sum_list (map sz [0..<CARD('b)])" by simp

  from lbs * have lbs_sum: "length bs = sum_list (map sz [0..<CARD('b)])" by simp
  have off_sz:  "(\<And>i. i < CARD('b) \<Longrightarrow> off i = sum_list (map sz [0..<i])) "
    unfolding off_def sz_def using sum_list_const_fun
    by auto

  have val_eq: "\<And>i. i < CARD('b) \<Longrightarrow> v i (take (sz i) (drop (off i) bs)) = take (sz i) (drop (off i) xbs)"
    unfolding off_def sz_def v_def xbs_def
    apply (simp add: to_bytes_def)
    apply (subst access_ti_array_index' [where xbs=bs, OF _ lbs])
      apply auto
    done

  have val_eq':
    "\<And>i. i < CARD('b) \<Longrightarrow>  (v i (take (sz i) (drop (off i) bs))) =
          (to_bytes (arr.[i]) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs)))"
    unfolding off_def sz_def v_def
    by simp

  have idx_eq: "\<And>i. i < CARD('b) \<Longrightarrow>
     (ptr_val p + word_of_nat (off i)) = (ptr_val (array_ptr_index p False i))"
    unfolding off_def array_ptr_index_def
    by (auto simp add:  c_type_class.ptr_add_def)


  note partition = heap_update_list_padding_fold_partition [where a="ptr_val p" and bs= xbs and pbs = bs and sz=sz and off=off and v=v and h=h and m="CARD('b)",
    OF no_overflow partition lxbs_sum partition_bs lbs_sum off_sz val_eq]
  show ?thesis
    apply (simp only: xbs_def [symmetric])
    apply (subst partition)
     apply (assumption)
    apply (rule fold_cong)
      apply (auto simp add: val_eq' idx_eq)
    done
qed

lemma heap_update_padding_array:
  fixes arr:: "('a::array_outer_max_size['b::array_max_count])"
  fixes p:: "('a['b]) ptr"
  assumes cgrd: "c_guard p"
  assumes lbs: "length bs = CARD('b) * size_of TYPE('a)"
  shows
"heap_update_padding p arr bs h =
    fold
      (\<lambda>i h. heap_update_padding (array_ptr_index p False i) (arr.[i]) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs)) h)
      [0..<CARD('b)] h"
  using heap_update_padding_list_array [OF cgrd lbs]
  by (simp only: heap_update_padding_def)

lemma heap_update_padding_array_pointless:
  fixes arr:: "('a::array_outer_max_size['b::array_max_count])"
  fixes p:: "('a['b]) ptr"
  assumes cgrd: "c_guard p"
  assumes lbs: "length bs = CARD('b) * size_of TYPE('a)"
  shows
"heap_update_padding p arr bs =
    fold
      (\<lambda>i h. heap_update_padding (array_ptr_index p False i) (arr.[i]) (take (size_of TYPE('a)) (drop (i * size_of TYPE('a)) bs)) h)
      [0..<CARD('b)]"
  using heap_update_padding_array [OF cgrd lbs]
  by (simp add: fun_eq_iff)

lemma c_guard_array_ptr_index:
  fixes p:: "(('a :: mem_type)['b :: finite]) ptr"
  assumes cgrd: "c_guard p"
  assumes bound: "n < CARD('b)"
  shows "c_guard (array_ptr_index p coerce n)"
  using cgrd bound
  apply (simp add: array_ptr_index_def c_guard_def)
  apply (clarsimp, safe)
  subgoal
    apply (simp add: ptr_aligned_def)
    by (metis ptr_aligned_def ptr_aligned_plus ptr_val_ptr_coerce)
  subgoal
    supply fun_upd_apply[simp del]
    apply (simp add: c_null_guard_def)
    apply (simp add: CTypesDefs.ptr_add_def field_simps)
    by (auto simp add: intvl_def)
      (metis (no_types, opaque_lifting) Abs_fnat_hom_mult add.commute group_cancel.add1 nat_index_bound word_of_nat_plus)
  done

lemma heap_update_array_update:
  assumes n: "n < CARD('b :: array_max_count)"
  assumes size: "CARD('b) * size_of TYPE('a :: array_outer_max_size) < 2 ^ addr_bitsize"
  assumes cgrd: "c_guard p"
  shows "heap_update p (Arrays.update (arr :: 'a['b]) n v) hp
       = heap_update (array_ptr_index p False n) v (heap_update p arr hp)"
 proof -

    have P: "\<And>x k. \<lbrakk> x < CARD('b); k < size_of TYPE('a) \<rbrakk>
         \<Longrightarrow> unat (of_nat x * of_nat (size_of TYPE('a)) + (of_nat k :: addr))
                 = x * size_of TYPE('a) + k"
    using size
    supply unsigned_of_nat [simp del]
    apply (cases "size_of TYPE('a)", simp_all)
    apply (cases "CARD('b)", simp_all)
    apply (subst unat_add_lem[THEN iffD1])
     apply (simp add: unat_word_ariths unat_of_nat less_Suc_eq_le)
    subgoal premises prems for x k nat nata
    proof -
      have "Suc x * size_of TYPE('a) < 2 ^ addr_bitsize"
        using prems 
        apply simp
        apply (erule order_le_less_trans[rotated], simp add: add_mono)
        done
      then show ?thesis using prems by simp
    qed
    apply (subst unat_mult_lem[THEN iffD1])
     apply (simp add: unat_of_nat unat_add_lem[THEN iffD1])
     apply (rule order_less_le_trans, erule order_le_less_trans[rotated],
            rule add_mono, simp+)
      apply (simp add: less_Suc_eq_le trans_le_add2)
     apply simp
    apply (simp add: unat_of_nat unat_add_lem[THEN iffD1])
    done

  let ?key_upd = "heap_update (array_ptr_index p False n) v"
  note commute = fold_commute_apply[where h="?key_upd"
      and xs="[Suc n ..< CARD('b)]", where g=f' and f=f' for f']

  from cgrd n
  have cgrd': "c_guard (array_ptr_index p False n)"
    by (rule c_guard_array_ptr_index)

  show ?thesis using n
    apply (simp add: heap_update_array [OF cgrd] split_upt_on_n[OF n]
                     )
    apply (subst commute)
    subgoal for x
      apply (rule ext, simp)
      apply (rule heap_update_commute, simp_all add: ptr_add_def)
      apply (simp add: array_ptr_index_def CTypesDefs.ptr_add_def intvl_def Suc_le_eq)
      apply (rule set_eqI, clarsimp)
      apply (drule word_unat.Rep_inject[THEN iffD2])
      apply (clarsimp simp: P nat_eq_add_iff1)
      apply (cases x, simp_all add: less_Suc_eq_le Suc_diff_le)
      done
    subgoal
      apply (subst heap_update_collapse)
      apply (simp cong: fold_cong')
      done
    done
qed


lemma heap_update_array_element'':
  fixes p' :: "(('a ::array_outer_max_size)['b::array_max_count]) ptr"
  fixes p :: "('a :: array_outer_max_size) ptr"
  fixes hp w
  assumes p: "p = array_ptr_index p' False n"
  assumes n: "n < CARD('b)"
  assumes cgrd: "c_guard p'"
  assumes size: "CARD('b) * size_of TYPE('a) < 2 ^ addr_bitsize"
  shows "heap_update p' (Arrays.update (h_val hp p') n w) hp
       = heap_update p w hp"
  apply (subst heap_update_array_update[OF n size cgrd])
  apply (simp add: heap_update_id p)
  done

lemmas heap_update_array_element'
    = heap_update_array_element''[simplified array_ptr_index_simps]

lemma (in array_outer_max_size) array_count_size:
  "CARD('b :: array_max_count) * size_of TYPE('a ) < 2 ^ addr_bitsize"
  using array_outer_max_size_ax[] array_max_count_ax[where 'a='b]
  apply (clarsimp dest!: nat_le_Suc_less_imp)
  apply (drule(1) mult_mono, simp+)
  done

lemmas heap_update_array_element
    = heap_update_array_element'[OF refl _ _ array_count_size]

primrec
  field_names_u :: "typ_uinfo \<Rightarrow> typ_uinfo \<Rightarrow>
      (qualified_field_name) list" and
  field_names_struct_u :: "typ_uinfo_struct \<Rightarrow> typ_uinfo \<Rightarrow>
      (qualified_field_name) list" and
  field_names_list_u :: "typ_uinfo_tuple list \<Rightarrow> typ_uinfo \<Rightarrow>
      (qualified_field_name) list" and
  field_names_tuple_u :: "typ_uinfo_tuple \<Rightarrow> typ_uinfo \<Rightarrow>
      (qualified_field_name) list"
where
  tufs0: "field_names_u (TypDesc algn st nm) t = (if t= (TypDesc algn st nm) then
         [[]] else field_names_struct_u st t)"

| tufs1: "field_names_struct_u (TypScalar m algn d) t = []"
| tufs2: "field_names_struct_u (TypAggregate xs) t = field_names_list_u xs t"

| tufs3: "field_names_list_u [] t = []"
| tufs4: "field_names_list_u (x#xs) t = field_names_tuple_u x t@field_names_list_u xs t"

| tufs5: "field_names_tuple_u (DTuple s f d) t = map (\<lambda>fs. f#fs) (field_names_u s t)"

lemma field_names_u_field_names_export_uinfo_conv:
  fixes t  :: "('a, 'b) typ_info" and
        st :: "('a, 'b) typ_info_struct" and
        ts :: "('a, 'b) typ_info_tuple list" and
        x  :: "('a, 'b) typ_info_tuple"
  shows
  "field_names_u (export_uinfo t) s = field_names t s"
  "field_names_struct_u (map_td_struct field_norm (\<lambda>_. ()) st) s = field_names_struct st s"
  "field_names_list_u (map_td_list field_norm (\<lambda>_. ()) ts) s  = field_names_list ts s"
  "field_names_tuple_u (map_td_tuple field_norm (\<lambda>_. ()) x) s  = field_names_tuple x s"
  by (induct t and st and ts and x ) (auto simp add: export_uinfo_def)


primrec
  all_field_names :: "('a, 'b) typ_desc \<Rightarrow>
      (qualified_field_name) list" and
  all_field_names_struct :: "('a, 'b) typ_struct \<Rightarrow>
      (qualified_field_name) list" and
  all_field_names_list :: "(('a, 'b) typ_desc, field_name, 'b) dt_tuple list \<Rightarrow>
      (qualified_field_name) list" and
  all_field_names_tuple :: "(('a, 'b) typ_desc, field_name, 'b) dt_tuple \<Rightarrow>
      (qualified_field_name) list"
where
  afs0: "all_field_names (TypDesc algn st nm) =
         [[]] @ all_field_names_struct st"

| afs1: "all_field_names_struct (TypScalar m algn d) = []"
| afs2: "all_field_names_struct (TypAggregate xs) = all_field_names_list xs"

| afs3: "all_field_names_list [] = []"
| afs4: "all_field_names_list (x#xs) = all_field_names_tuple x @ all_field_names_list xs"

| afs5: "all_field_names_tuple (DTuple s f d) = map (\<lambda>fs. f#fs) (all_field_names s)"

lemma field_lookup_all_field_names:
  fixes t::"('a, 'b) typ_desc"
  and st::"('a, 'b) typ_struct"
  and ts::"('a, 'b) typ_tuple list"
  and x::"('a, 'b) typ_tuple"
shows
  "field_lookup t f m = Some (s, n) \<Longrightarrow> f \<in> set (all_field_names t)" and
  "field_lookup_struct st f m = Some (s, n) \<Longrightarrow> f \<in> set (all_field_names_struct st)" and
  "field_lookup_list ts f m = Some (s, n) \<Longrightarrow> f \<in> set (all_field_names_list ts)" and
  "field_lookup_tuple x f m = Some (s, n) \<Longrightarrow> f \<in> set (all_field_names_tuple x)"
proof (induct t and st and ts and x arbitrary: f m n s and f m n s and f m n s and f m n s)
  case (TypDesc nat typ_struct list)
  then show ?case by (auto split: if_split_asm)
next
  case (TypScalar nat1 nat2 a)
  then show ?case by auto
next
  case (TypAggregate list)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case  by (auto split: option.splits)
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by (auto split: if_split_asm)
     (metis imageI list.exhaust_sel)
qed

lemma field_names_subset_all_field_names:
  fixes t  :: "typ_uinfo" and
        st :: "typ_uinfo_struct" and
        ts :: "typ_uinfo_tuple list" and
        x  :: "typ_uinfo_tuple"
      shows
 "set (field_names_u t s) \<subseteq> set (all_field_names t)"
 "set (field_names_struct_u st s) \<subseteq> set (all_field_names_struct st)"
 "set (field_names_list_u ts s) \<subseteq> set (all_field_names_list ts)"
 "set (field_names_tuple_u x s) \<subseteq> set (all_field_names_tuple x)"
     by (induct t and st and ts and x arbitrary: s and s and s and s) auto


lemma empty_all_field_names:
  fixes t  :: "typ_uinfo" and
        st :: "typ_uinfo_struct" and
        ts :: "typ_uinfo_tuple list" and
        x  :: "typ_uinfo_tuple"
      shows
 "[] \<in> set (all_field_names t)"
 "[] \<notin> set (all_field_names_struct st)"
 "[] \<notin> set (all_field_names_list ts)"
 "[] \<notin> set (all_field_names_tuple x)"
  by (induct t and st and ts and x ) auto

lemma empty_field_names_u:
  fixes t  :: "typ_uinfo" and
        st :: "typ_uinfo_struct" and
        ts :: "typ_uinfo_tuple list" and
        x  :: "typ_uinfo_tuple"
      shows
 "True"
 "[] \<notin> set (field_names_struct_u st s)"
 "[] \<notin> set (field_names_list_u ts s)"
 "[] \<notin> set (field_names_tuple_u x s)"
  by (induct t and st and ts and x ) auto


lemma non_empty_field_names_u:
  fixes t  :: "typ_uinfo" and
        st :: "typ_uinfo_struct" and
        ts :: "typ_uinfo_tuple list" and
        x  :: "typ_uinfo_tuple"
      shows
 "field_names_u t s \<noteq> [] \<Longrightarrow> \<exists>n. (s, n) \<in> td_set t m"
 "(field_names_struct_u st s) \<noteq> [] \<Longrightarrow> \<exists>n. (s, n) \<in> td_set_struct st m"
 "(field_names_list_u ts s) \<noteq> [] \<Longrightarrow> \<exists>n. (s, n) \<in> td_set_list ts m"
 "(field_names_tuple_u x s) \<noteq> [] \<Longrightarrow> \<exists>n. (s, n) \<in> td_set_tuple x m"
     by (induct t and st and ts and x arbitrary: s m and s m and s m and s m) fastforce+


lemma td_set_size:
 "(s, n) \<in> td_set t m \<Longrightarrow> size s \<le> size t"
 "(s, n) \<in> td_set_struct st m \<Longrightarrow> size s \<le> size st"
 "(s, n) \<in> td_set_list ts m \<Longrightarrow> \<exists>t \<in> set ts. size s \<le> size (dt_fst t)"
 "(s, n) \<in> td_set_tuple x m \<Longrightarrow> size s \<le> size (dt_fst x)"
proof (induct t and st and ts and x arbitrary: s n m and s n m and s n m and s n m)
  case (TypDesc nat typ_struct list)
  then show ?case by fastforce
next
  case (TypScalar nat1 nat2 a)
  then show ?case by auto
next
  case (TypAggregate list)
  then show ?case by (auto simp add: less_Suc_eq less_imp_le td_set_list_size_lte)
next
  case Nil_typ_desc
  then show ?case by simp
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case by auto
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by auto
qed

lemma td_set_field_names_nonempty:
 "(s, n) \<in> td_set t m \<Longrightarrow> field_names t (export_uinfo s) \<noteq> []"
 "(s, n) \<in> td_set_struct st m \<Longrightarrow> field_names_struct st (export_uinfo s) \<noteq> []"
 "(s, n) \<in> td_set_list ts m \<Longrightarrow> field_names_list ts (export_uinfo s) \<noteq> []"
 "(s, n) \<in> td_set_tuple x m \<Longrightarrow> field_names_tuple x (export_uinfo s) \<noteq> []"
  by (induct t and st and ts and x arbitrary: n m and n m and n m and n m) auto

lemma sub_typ_field_names_nonempty:
  assumes s_t: "s \<le> t"
  shows "field_names t (export_uinfo s) \<noteq> []"
proof -
  from s_t obtain n where "(s, n) \<in> td_set t 0"
    by (auto simp add: typ_tag_le_def)
  from td_set_field_names_nonempty (1) [OF this] show ?thesis.
qed

lemma sub_typ_export_uinfo_mono:
  assumes s_t: "s \<le> t"
  shows "export_uinfo s \<le> export_uinfo t"
  using s_t
  by (meson td_set_export_uinfoD typ_tag_le_def)

lemma descriptor_not_in_self: "(TypDesc algn st nm, n) \<notin> td_set_struct st m"
proof
  assume "(TypDesc algn st nm, n) \<in> td_set_struct st m"
  from td_set_size(2) [OF this] show False by simp
qed

lemma field_names_struct_descriptor_empty: "field_names_struct_u st (TypDesc algn st nm) = []"
  using descriptor_not_in_self non_empty_field_names_u(2)
  by blast

lemma all_field_names_exists_field_names_u:
  fixes t  :: "typ_uinfo" and
        st :: "typ_uinfo_struct" and
        ts :: "typ_uinfo_tuple list" and
        x  :: "typ_uinfo_tuple"
      shows
 "f \<in> set (all_field_names t) \<Longrightarrow> \<exists>s. f \<in> set (field_names_u t s)"
 "f \<in> set (all_field_names_struct st) \<Longrightarrow> \<exists>s. f \<in> set (field_names_struct_u st s)"
 "f \<in> set (all_field_names_list ts) \<Longrightarrow> \<exists>s. f \<in> set (field_names_list_u ts s)"
 "f \<in> set (all_field_names_tuple x) \<Longrightarrow> \<exists>s. f \<in> set (field_names_tuple_u x s)"
proof (induct t and st and ts and x arbitrary: f and f and f and f)
case (TypDesc algn st nm)
  then show ?case
  proof (cases "f = []")
    case True
    with TypDesc show ?thesis by auto
  next
    case False
    with TypDesc obtain s where s: "f \<in> set (field_names_struct_u st s)" by auto
    with field_names_struct_descriptor_empty have "s \<noteq> TypDesc algn st nm" by auto
    with s False TypDesc show ?thesis by auto
  qed
next
  case (TypScalar nat1 nat2 a)
  then show ?case by auto
next
  case (TypAggregate list)
then show ?case by auto
next
case Nil_typ_desc
then show ?case by auto
next
case (Cons_typ_desc dt_tuple list)
then show ?case by auto
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case
    by auto
      (meson empty_all_field_names(1) imageI)
qed

theorem all_field_names_union_field_names_u_conv: "set (all_field_names t) = (\<Union>s. set (field_names_u t s))"
proof
  show "set (all_field_names t) \<subseteq> (\<Union>s. set (field_names_u t s))"
    using all_field_names_exists_field_names_u
    by auto
next
  show "(\<Union>s. set (field_names_u t s)) \<subseteq> set (all_field_names t)"
    using field_names_subset_all_field_names(1)
    by auto
qed

corollary all_field_names_union_field_names_export_uinfo_conv:
  "set (all_field_names (export_uinfo t)) = (\<Union>s. set (field_names t s))"
proof -
  have "(\<Union>s. set (field_names t s)) = (\<Union>s. set (field_names_u (export_uinfo t) s))"
    by (simp add: field_names_u_field_names_export_uinfo_conv)
  with all_field_names_union_field_names_u_conv show ?thesis by metis
qed

lemma filter_same_eq: "(\<And>x. x \<in> set xs \<Longrightarrow> P x = Q x) \<Longrightarrow> filter P xs = filter Q xs"
  by (induct xs) auto

lemma field_lookup_tuple_hd_notin: "n \<noteq> dt_snd x \<Longrightarrow> field_lookup_tuple x (n # ns) m = None"
  by (cases x) auto

lemma field_lookup_list_hd_notin: "n \<notin> dt_snd ` set xs \<Longrightarrow> field_lookup_list xs (n # ns) m = None"
  by (induct xs arbitrary: m)
     (auto split: option.splits simp add: field_lookup_tuple_hd_notin)

lemma list_append_eq_split: "xs1 = xs2 \<Longrightarrow> ys1 = ys2 \<Longrightarrow> (xs1 @ ys1) = (xs2 @ ys2)"
  by simp

lemma field_names_u_filter_all_field_names_conv:
  fixes t  :: "typ_uinfo" and
        st :: "typ_uinfo_struct" and
        ts :: "typ_uinfo_tuple list" and
        x  :: "typ_uinfo_tuple"
      shows
 "wf_desc t \<Longrightarrow>
   (field_names_u t s) = filter (\<lambda>f. \<exists>n. field_lookup t f 0 = Some (s, n)) (all_field_names t)"
 "wf_desc_struct st \<Longrightarrow>
   field_names_struct_u st s = filter (\<lambda>f. \<exists>n. field_lookup_struct st f 0 = Some (s, n)) (all_field_names_struct st)"
 "wf_desc_list ts \<Longrightarrow>
   field_names_list_u ts s = filter (\<lambda>f. \<exists>n. field_lookup_list ts f 0 = Some (s, n)) (all_field_names_list ts)"
 "wf_desc_tuple x \<Longrightarrow>
   field_names_tuple_u x s = filter (\<lambda>f. \<exists>n. field_lookup_tuple x f 0 = Some (s, n)) (all_field_names_tuple x)"
proof (induct t and st and ts and x arbitrary: s and s and s and s)
 case (TypDesc algn st nm)
  then show ?case
    apply (clarsimp simp add: empty_all_field_names, safe)
     apply (smt (verit, best) descriptor_not_in_self empty_all_field_names(2)
        filter_False td_set_struct_field_lookup_structD)
    by (metis (no_types, opaque_lifting) field_lookup_struct_empty option.simps(3))
next
  case (TypScalar n algn x)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x xs)
  from Cons_typ_desc.prems obtain
    wf_x: "wf_desc_tuple x" and
    wf_xs: "wf_desc_list xs" and
    distinct: "dt_snd x \<notin> dt_snd ` set xs" by clarsimp
  have eq1:
    "filter (\<lambda>f. \<exists>n. field_lookup_tuple x f 0 = Some (s, n)) (all_field_names_tuple x) =
    filter
     (\<lambda>f. \<exists>n. (case field_lookup_tuple x f 0 of
                None \<Rightarrow> field_lookup_list xs f (0 + size_td (dt_fst x))
                | Some x \<Rightarrow> Some x) =
               Some (s, n)) (all_field_names_tuple x)"
    apply (rule filter_same_eq)
    apply (cases x)
    subgoal for nm t' _
      using distinct
      apply (auto split: option.splits simp add: field_lookup_list_hd_notin)
      done
    done
  have eq2: "filter (\<lambda>f. \<exists>n. field_lookup_list xs f 0 = Some (s, n))
     (all_field_names_list xs) =
    filter
     (\<lambda>f. \<exists>n. (case field_lookup_tuple x f 0 of
                None \<Rightarrow> field_lookup_list xs f (0 + size_td (dt_fst x))
                | Some x \<Rightarrow> Some x) =
               Some (s, n))
     (all_field_names_list xs)"
    apply (rule filter_same_eq)
    apply (cases x)
    subgoal for nm t' _
      using distinct Cons_typ_desc.hyps(2)[OF wf_xs]
      by (smt (verit) all_field_names_exists_field_names_u(3) dt_prj_simps(2)
          field_lookup_list_None field_lookup_list_offsetD field_lookup_offset'(3)
          fl5 hd_Cons_tl mem_Collect_eq option.case(1) option.simps(3) set_filter)
    done


  show ?case
    by (simp add:  Cons_typ_desc.hyps(1)[OF wf_x]  Cons_typ_desc.hyps(2)[OF wf_xs] eq1 eq2 )
next
  case (DTuple_typ_desc t' nm _)
  then show ?case
    by (auto simp add: filter_map intro: filter_same_eq )
qed

lemma all_field_names_export_uinfo':
  fixes t:: "('a, 'b) typ_info"
  and st:: "('a, 'b) typ_info_struct"
  and ts::"('a, 'b) typ_info_tuple list"
  and x::"('a, 'b) typ_info_tuple"
shows
"all_field_names (map_td field_norm (\<lambda>_. ()) t) = all_field_names t"
"all_field_names_struct (map_td_struct field_norm (\<lambda>_. ()) st) = all_field_names_struct st"
"all_field_names_list  (map_td_list field_norm (\<lambda>_. ()) ts) = all_field_names_list ts"
"all_field_names_tuple (map_td_tuple field_norm (\<lambda>_. ()) x) = all_field_names_tuple x"
  by (induct t and st and ts and x) auto

lemma all_field_names_export_uinfo:
"all_field_names (export_uinfo t) = all_field_names t"
  by (simp add: export_uinfo_def all_field_names_export_uinfo')

lemma "inj (#)"
  by (metis inj_onI list.inject)

lemma distinct_map_cons: "distinct xs \<Longrightarrow>  distinct (map ((#) ys) xs)"
  by (induct xs) auto

lemma all_field_names_list_conv: "all_field_names_list xs =
   concat (map (\<lambda>x. map ((#) (dt_snd x)) ((all_field_names o dt_fst) x)) xs)"
  apply (induct xs)
   apply simp
  subgoal for x1 xs
  apply (cases x1)
    apply auto
    done
  done



lemma distinct_all_field_names:
  fixes t  :: "('a, 'b) typ_info" and
        st :: "('a, 'b) typ_info_struct" and
        ts :: "('a, 'b) typ_info_tuple list" and
        x  :: "('a, 'b) typ_info_tuple"
  shows
  "wf_desc t \<Longrightarrow> distinct (all_field_names t)" and
  "wf_desc_struct st \<Longrightarrow> distinct (all_field_names_struct st)" and
  "wf_desc_list ts \<Longrightarrow> distinct (all_field_names_list ts)" and
  "wf_desc_tuple x \<Longrightarrow> distinct (all_field_names_tuple x)"
proof (induct t and st and ts and x)
  case (TypDesc algn st nm)
  then show ?case
    by auto (metis all_field_names_export_uinfo'(2) empty_all_field_names(2))
next
  case (TypScalar n algn x)
  then show ?case by auto
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x xs)
  then show ?case apply (cases x) by (auto simp add: all_field_names_list_conv)
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case
    by (auto simp add: distinct_map_cons)
qed

lemma td_set_field_names_u_nonempty:
 "(s, n) \<in> td_set t m \<Longrightarrow> field_names_u t s \<noteq> []"
 "(s, n) \<in> td_set_struct st m \<Longrightarrow> field_names_struct_u st s \<noteq> []"
 "(s, n) \<in> td_set_list ts m \<Longrightarrow> field_names_list_u ts s \<noteq> []"
 "(s, n) \<in> td_set_tuple x m \<Longrightarrow> field_names_tuple_u x s \<noteq> []"
  by (induct t and st and ts and x arbitrary: n m and n m and n m and n m) auto

lemma field_lookup_export_uinfo_Some_rev:
  "field_lookup (export_uinfo t) f n = Some (s, k) \<Longrightarrow> \<exists>s'. field_lookup t f n = Some (s', k) \<and> s = export_uinfo s'"
  by (simp add: export_uinfo_def field_lookup_map map_td_flr_def split: option.splits prod.splits)

lemma wf_desc_export_uinfo_pres:
  fixes t  :: "('a, 'b) typ_info" and
        st :: "('a, 'b) typ_info_struct" and
        ts :: "('a, 'b) typ_info_tuple list" and
        x  :: "('a, 'b) typ_info_tuple"
  shows
  "wf_desc t \<Longrightarrow> wf_desc (export_uinfo t)"
  "wf_desc_struct st \<Longrightarrow> wf_desc_struct (map_td_struct field_norm (\<lambda>_. ()) st)"
  "wf_desc_list ts \<Longrightarrow> wf_desc_list (map_td_list field_norm (\<lambda>_. ()) ts)"
  "wf_desc_tuple x \<Longrightarrow> wf_desc_tuple (map_td_tuple field_norm (\<lambda>_. ()) x)"
     apply (induct t and st and ts and x ) 
    by (auto simp add: export_uinfo_def)
     (metis imageI mat4 wf_desc_list.wfd4 wf_desc_map(3))


primrec
  toplevel_field_names :: "('a, 'b) typ_desc \<Rightarrow>
      (field_name) list" and
  toplevel_field_names_struct :: "('a, 'b) typ_struct \<Rightarrow>
      (field_name) list" and
  toplevel_field_names_list :: "('a, 'b) typ_tuple list \<Rightarrow>
      (field_name) list" and
  toplevel_field_names_tuple :: "('a, 'b) typ_tuple \<Rightarrow>
      (field_name) list"
where
   "toplevel_field_names (TypDesc algn st nm) = toplevel_field_names_struct st"

| "toplevel_field_names_struct (TypScalar m algn d) = []"
| "toplevel_field_names_struct (TypAggregate xs) = toplevel_field_names_list xs"

| "toplevel_field_names_list [] = []"
| "toplevel_field_names_list (x#xs) = toplevel_field_names_tuple x @ toplevel_field_names_list xs"

| "toplevel_field_names_tuple (DTuple s f d) = [f]"


lemma all_field_names_root: "\<exists>xs. all_field_names t = [[]] @ xs"
  by (cases t) simp

lemma toplevel_field_names_all_field_names:
  fixes t:: "('a, 'b) typ_desc"
  and st:: "('a, 'b) typ_struct"
  and ts::"('a, 'b) typ_tuple list"
  and x::"('a, 'b) typ_tuple"
shows
"f \<in> set (toplevel_field_names t) \<Longrightarrow> [f] \<in> set (all_field_names t)"
"f \<in> set (toplevel_field_names_struct st) \<Longrightarrow> [f] \<in> set (all_field_names_struct st)"
"f \<in> set (toplevel_field_names_list ts) \<Longrightarrow> [f] \<in> set (all_field_names_list ts)"
"f \<in> set (toplevel_field_names_tuple x) \<Longrightarrow> [f] \<in> set (all_field_names_tuple x)"
     apply (induct t and st and ts and x)
  by auto
    (metis all_field_names_root append_Cons imageI list.set_intros(1))

lemma append_eq_same_prefixI: "ys = zs \<Longrightarrow> xs @ ys = xs @ zs"
  by simp

lemma toplevel_field_names_field_lookup:
  fixes t:: "('a, 'b) typ_info"
  and st:: "('a, 'b) typ_info_struct"
  and ts::"('a, 'b) typ_info_tuple list"
  and x::"('a, 'b) typ_info_tuple"
shows
"f \<in> set (toplevel_field_names t) \<Longrightarrow> wf_desc t \<Longrightarrow>
  \<exists>s n. field_lookup t [f] m = Some (s, m + n)"

"f \<in> set (toplevel_field_names_struct st) \<Longrightarrow> wf_desc_struct st \<Longrightarrow>
  \<exists>s n. field_lookup_struct st [f] m = Some (s, m + n)"

"f \<in> set (toplevel_field_names_list ts) \<Longrightarrow> wf_desc_list ts \<Longrightarrow>
  \<exists>s n. field_lookup_list ts [f] m = Some (s, m + n)"

"f \<in> set (toplevel_field_names_tuple x) \<Longrightarrow> wf_desc_tuple x \<Longrightarrow>
  \<exists>s n. field_lookup_tuple x [f] m = Some (s, m + n)"
proof (induct t and st and ts and x arbitrary: f m and f m and f m and  f m)
case (TypDesc algn st nm)
  then show ?case by simp
next
  case (TypScalar sz algn d)
  then show ?case by simp
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto
  then show ?case using Cons_typ_desc
    by auto
     (metis (no_types, opaque_lifting) add.assoc)
next
  case (DTuple_typ_desc d nm y)
  then show ?case by auto
qed

lemma partition_toplevel_field_names:
  fixes t:: "('a, 'b) typ_info"
  and st:: "('a, 'b) typ_info_struct"
  and ts::"('a, 'b) typ_info_tuple list"
  and x::"('a, 'b) typ_info_tuple"
shows
"length bs = size_td t \<Longrightarrow> aggregate t \<Longrightarrow> wf_desc t \<Longrightarrow>
  concat (map (\<lambda>f. take (size_td (fst (the (field_lookup t [f] n))))
                    (drop (snd (the (field_lookup t [f] n)) - n) bs))
                      (toplevel_field_names t)) = bs"

"length bs = size_td_struct st \<Longrightarrow> aggregate_struct st \<Longrightarrow> wf_desc_struct st \<Longrightarrow>
  concat (map (\<lambda>f. take (size_td (fst (the (field_lookup_struct st [f] n))))
                    (drop (snd (the (field_lookup_struct st [f] n)) - n) bs))
                     (toplevel_field_names_struct st)) = bs"

"length bs = size_td_list ts \<Longrightarrow> wf_desc_list ts \<Longrightarrow>
  concat (map (\<lambda>f. take (size_td (fst (the (field_lookup_list ts [f] n))))
                    (drop (snd (the (field_lookup_list ts [f] n)) - n) bs))
                     (toplevel_field_names_list ts)) = bs"

"length bs = size_td_tuple x \<Longrightarrow> wf_desc_tuple x \<Longrightarrow>
  concat (map (\<lambda>f. take (size_td (fst (the (field_lookup_tuple x [f] n))))
                    (drop (snd (the (field_lookup_tuple x [f] n)) - n) bs))
                     (toplevel_field_names_tuple x)) = bs"
proof (induct t and st and ts and x arbitrary: bs n and bs n and bs n and bs n)
case (TypDesc algn st nm)
  then show ?case by simp
next
  case (TypScalar sz algn d)
  then show ?case by simp
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto
  from Cons_typ_desc.prems obtain
    lbs: "length bs = size_td_tuple x + size_td_list fs" and
    wf_desc_x: "wf_desc_tuple (DTuple d nm y)" and
    nm_notin:  "nm \<notin> dt_snd ` set fs" and
    wf_desc_fs: "wf_desc_list fs"

    by (auto simp add: x)

  from nm_notin have nm_notin': "nm \<notin> set (toplevel_field_names_list fs)"
  proof (induct fs)
    case Nil
    then show ?case by simp
  next
    case (Cons f1 fs)
    then show ?case by (cases f1) auto
  qed

  from lbs have l_take: "length (take (size_td d) bs) = size_td d"
    by (simp add: x)

  from lbs have l_drop: "length (drop (size_td d) bs) = size_td_list fs"
    by (simp add: x)


  from lbs have bs_take_drop: "bs = take (size_td d) bs @ drop (size_td d) bs"
    by (simp add: x)
  note hyp = Cons_typ_desc.hyps(2) [OF l_drop wf_desc_fs, where n= "(n + size_td d)"]

  show ?case
    apply (simp add: x)
    apply (simp cong: if_cong option.case_cong)
    apply (subst (3) bs_take_drop)
    apply (rule append_eq_same_prefixI)
    apply (subst hyp [symmetric])
    apply (rule arg_cong [where f = concat])
    apply (rule map_cong [OF refl])
    using nm_notin'
    apply auto
    thm toplevel_field_names_field_lookup(3)[OF _ wf_desc_fs]
    apply (frule toplevel_field_names_field_lookup(3) [OF _ wf_desc_fs, where m = "(n + size_td d)" ])
    by auto
     (metis add.commute)
next
  case (DTuple_typ_desc d nm y)
  then show ?case by auto
qed


lemma toplevel_field_names_export_uinfo':
  fixes t:: "('a, 'b) typ_info"
  and st:: "('a, 'b) typ_info_struct"
  and ts::"('a, 'b) typ_info_tuple list"
  and x::"('a, 'b) typ_info_tuple"
shows
"toplevel_field_names (map_td field_norm (\<lambda>_. ()) t) = toplevel_field_names t"
"toplevel_field_names_struct (map_td_struct field_norm (\<lambda>_. ()) st) = toplevel_field_names_struct st"
"toplevel_field_names_list (map_td_list field_norm (\<lambda>_. ()) ts) = toplevel_field_names_list ts"
"toplevel_field_names_tuple (map_td_tuple field_norm (\<lambda>_. ()) x) = toplevel_field_names_tuple x"
  by (induct t and st and ts and x)  auto

lemma toplevel_field_names_export_uinfo:
"toplevel_field_names (export_uinfo t) = toplevel_field_names t"
  using toplevel_field_names_export_uinfo' by (simp add: export_uinfo_def)

lemma (in xmem_type) xmem_type_partition_toplevel_field_names:
  assumes aggregate: "aggregate (typ_info_t TYPE('a))"
  assumes lbs: "length bs = size_of (TYPE('a))"
  shows "concat (map (\<lambda>f. take (size_td (fst (the (field_lookup (typ_info_t TYPE('a)) [f] 0))))
                    (drop (snd (the (field_lookup (typ_info_t TYPE('a)) [f] 0))) bs))
                      (toplevel_field_names (typ_info_t TYPE('a)))) = bs"
  using partition_toplevel_field_names(1) [OF lbs [simplified size_of_def] aggregate wf_desc, where n=0]
  by simp

lemma toplevel_field_names_sum_list_size:
  fixes t:: "('a, 'b) typ_info"
  and st:: "('a, 'b) typ_info_struct"
  and ts::"('a, 'b) typ_info_tuple list"
  and x::"('a, 'b) typ_info_tuple"
shows
"aggregate t \<Longrightarrow> wf_desc t \<Longrightarrow>
  sum_list (map (\<lambda>f. size_td (fst (the (field_lookup t [f] n)))) (toplevel_field_names t)) =
  size_td t"

"aggregate_struct st \<Longrightarrow> wf_desc_struct st \<Longrightarrow>
  sum_list (map (\<lambda>f. size_td (fst (the (field_lookup_struct st [f] n)))) (toplevel_field_names_struct st)) =
  size_td_struct st"

"wf_desc_list ts \<Longrightarrow>
  sum_list (map (\<lambda>f. size_td (fst (the (field_lookup_list ts [f] n)))) (toplevel_field_names_list ts)) =
  size_td_list ts"

"wf_desc t \<Longrightarrow>
  sum_list (map (\<lambda>f. size_td (fst (the (field_lookup_tuple x [f] n)))) (toplevel_field_names_tuple x)) =
  size_td_tuple x"
proof (induct t and st and ts and x arbitrary:  n and n and n and  n)
case (TypDesc algn st nm)
  then show ?case by simp
next
  case (TypScalar sz algn d)
  then show ?case by simp
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto


  from Cons_typ_desc.prems obtain
    wf_desc_x: "wf_desc_tuple (DTuple d nm y)" and
    nm_notin:  "nm \<notin> dt_snd ` set fs" and
    wf_desc_fs: "wf_desc_list fs"
    by (auto simp add: x)

  from nm_notin have nm_notin': "nm \<notin> set (toplevel_field_names_list fs)"
  proof (induct fs)
    case Nil
    then show ?case by simp
  next
    case (Cons f1 fs)
    then show ?case by (cases f1) auto
  qed

  note hyp = Cons_typ_desc.hyps(2) [OF wf_desc_fs, where n= "(n + size_td d)"]

  show ?case
    apply (simp add: x)
    apply (simp cong: if_cong option.case_cong)
    using nm_notin' hyp
    by (smt (verit, best) map_eq_conv option.simps(4))
next
  case (DTuple_typ_desc d nm y)
  then show ?case by auto
qed


lemma toplevel_field_names_sum_list_offset:
  fixes t:: "('a, 'b) typ_info"
  and st:: "('a, 'b) typ_info_struct"
  and ts::"('a, 'b) typ_info_tuple list"
  and x::"('a, 'b) typ_info_tuple"
shows
"aggregate t \<Longrightarrow> wf_desc t \<Longrightarrow> i < length (toplevel_field_names t) \<Longrightarrow>
  sum_list (map (\<lambda>i. size_td (fst (the (field_lookup t [(toplevel_field_names t) ! i] n)))) [0..<i]) =
  (snd (the (field_lookup t [(toplevel_field_names t) ! i] n)) - n)"

"aggregate_struct st \<Longrightarrow> wf_desc_struct st \<Longrightarrow> i < length (toplevel_field_names_struct st) \<Longrightarrow>
  sum_list (map (\<lambda>i. size_td (fst (the (field_lookup_struct st [(toplevel_field_names_struct st) ! i] n)))) [0..<i]) =
  (snd (the (field_lookup_struct st [(toplevel_field_names_struct st) ! i] n)) - n)"

"wf_desc_list ts \<Longrightarrow> i < length (toplevel_field_names_list ts) \<Longrightarrow>
  sum_list (map (\<lambda>i. size_td (fst (the (field_lookup_list ts [(toplevel_field_names_list ts) ! i] n)))) [0..<i]) =
  (snd (the (field_lookup_list ts [(toplevel_field_names_list ts) ! i] n)) - n)"

"wf_desc_tuple x \<Longrightarrow> i < length (toplevel_field_names_tuple x) \<Longrightarrow>
  sum_list (map (\<lambda>i. size_td (fst (the (field_lookup_tuple x [(toplevel_field_names_tuple x) ! i] n)))) [0..<i]) =
  (snd (the (field_lookup_tuple x [(toplevel_field_names_tuple x) ! i] n)) - n)"

proof (induct t and st and ts and x arbitrary:  n i and n i and n i and  n i)
case (TypDesc algn st nm)
  then show ?case by simp
next
  case (TypScalar sz algn d)
  then show ?case by simp
next
  case (TypAggregate ts)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case by auto
next
  case (Cons_typ_desc x fs)
  obtain d nm y where x: "x = DTuple d nm y" by (cases x) auto


  from Cons_typ_desc.prems obtain
    wf_desc_x: "wf_desc_tuple (DTuple d nm y)" and
    nm_notin:  "nm \<notin> dt_snd ` set fs" and
    wf_desc_fs: "wf_desc_list fs" and
    i_bound: "i < Suc (length (toplevel_field_names_list fs))"
    by (auto simp add: x)

  from nm_notin have nm_notin': "nm \<notin> set (toplevel_field_names_list fs)"
  proof (induct fs)
    case Nil
    then show ?case by simp
  next
    case (Cons f1 fs)
    then show ?case by (cases f1) auto
  qed

  note hyp = Cons_typ_desc.hyps(2) [OF wf_desc_fs, where n= "(n + size_td d)"]

  from nm_notin' i_bound have nm_eq_conv: "nm = (nm # toplevel_field_names_list fs) ! i \<longleftrightarrow> i = 0 "
    apply (cases i)
     apply simp
    apply (simp)
    using nth_mem by blast


  show ?case
  proof (cases i)
    case 0
    then show ?thesis by (simp add: x)
  next
    case (Suc i')

    with i_bound have i'_bound: "i' < length (toplevel_field_names_list fs)" by simp
    have split: "[0..<Suc i'] = 0 # [1..<Suc i']"
      by (simp add: upt_rec)

    have sum_eq:
      "(\<Sum>i\<leftarrow>[0..<i']. size_td
                     (fst (the (case if nm = toplevel_field_names_list fs ! i
                                     then Some (d, n) else None of
                                None \<Rightarrow>
                                  field_lookup_list fs
                                   [toplevel_field_names_list fs ! i] (n + size_td d)
                                | Some x2 \<Rightarrow> Some x2)))) =
       (\<Sum>i\<leftarrow>[0..<i']. size_td
                     (fst (the (field_lookup_list fs [toplevel_field_names_list fs ! i]
                                 (n + size_td d)))))"
      apply (rule arg_cong [where f=sum_list])
      apply (rule map_cong [OF refl])
      using nm_notin' i'_bound
      apply auto
      done

    show ?thesis
      apply (simp add: x)
      apply (clarsimp cong: if_cong option.case_cong simp add: nm_eq_conv)
      apply (subst Suc)
      apply (subst split)
      apply (simp only: list.map sum_list.Cons)
      apply (subst sum_list_Suc_index_shift)
      apply (simp add: Suc)
      apply (simp cong: if_cong option.case_cong)
      apply (subst sum_eq)
      apply (subst hyp [OF i'_bound])
      using toplevel_field_names_field_lookup(3)
        [where f="toplevel_field_names_list fs ! i'" and ts = fs and m="(n + size_td d)", OF _ wf_desc_fs] i'_bound
      apply clarsimp
      done
  qed
next
  case (DTuple_typ_desc d nm y)
  then show ?case by auto
qed

lemma sum_list_upt_map_nth_conv: "sum_list (map (\<lambda>i. g (xs ! i)) [0..<length xs]) = sum_list (map g xs)"
proof -
  from map_nth have eq1:  "map ((!) xs) [0..<length xs] = xs" .
  from map_map [where f=g and g="((!) xs)"]
  have eq2: "map g (map ((!) xs) [0..<length xs]) = map (g \<circ> (!) xs) [0..<length xs]" .
  from eq1 eq2
  show ?thesis
    by (simp add: comp_def)
qed


lemma toplevel_field_names_empty_typ_info: "toplevel_field_names (empty_typ_info algn tn) = []"
  by (simp add: empty_typ_info_def)

lemma toplevel_field_names_no_padding_empty_typ_info:
  "filter (Not o padding_field_name) (toplevel_field_names (empty_typ_info algn tn)) = []"
  by (simp add: empty_typ_info_def)

lemma toplevel_field_names_list_append [simp]:
  "toplevel_field_names_list (xs @ ys) = toplevel_field_names_list xs @ toplevel_field_names_list ys"
  by (induct xs) auto

lemma toplevel_field_names_extend_ti:
  fixes
  t :: "'a xtyp_info" and
  st :: "'a xtyp_info_struct" and
  ts :: "'a xtyp_info_tuple list" and
  x :: "'a xtyp_info_tuple"
  shows
  "toplevel_field_names (extend_ti t s n fn d) = toplevel_field_names t @ [fn]"
  "toplevel_field_names_struct (extend_ti_struct st s fn d) = toplevel_field_names_struct st @ [fn]"
  "toplevel_field_names_list ts = toplevel_field_names_list ts"
  "toplevel_field_names_tuple x = toplevel_field_names_tuple x"
  by (induct t and st and ts and x) auto

lemma toplevel_field_names_adjust_ti':
  fixes
  t :: "'a xtyp_info" and
  st :: "'a xtyp_info_struct" and
  ts :: "'a xtyp_info_tuple list" and
  x :: "'a xtyp_info_tuple"
  shows
"toplevel_field_names (map_td (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) t) =
  toplevel_field_names t"
"toplevel_field_names_struct (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) st) =
  toplevel_field_names_struct st"
"toplevel_field_names_list (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) ts) =
  toplevel_field_names_list ts"
"toplevel_field_names_tuple (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) x) =
  toplevel_field_names_tuple x"
by  (induct t and st and ts and x) (auto)

lemma toplevel_field_names_adjust_ti:
  "toplevel_field_names (adjust_ti t acc upd) = toplevel_field_names t"
  by (simp add: toplevel_field_names_adjust_ti' adjust_ti_def)

lemma padding_field_name_pad: "padding_field_name (foldl (@) ''!pad_'' xs)"
  by (auto simp add: padding_field_name_def foldl_conv_concat)

lemma toplevel_field_names_no_padding_ti_pad_combine:
  "filter (Not o padding_field_name) (toplevel_field_names (ti_pad_combine n t)) =
       filter (Not o padding_field_name) (toplevel_field_names t)"
  by (simp add: ti_pad_combine_def Let_def  toplevel_field_names_extend_ti(1) padding_field_name_pad)

lemma toplevel_field_names_ti_pad_combine:
  "(toplevel_field_names (ti_pad_combine n t)) =
      toplevel_field_names t @ [foldl (@) ''!pad_'' (CompoundCTypes.field_names_list t)]"
  by (simp add: ti_pad_combine_def Let_def  toplevel_field_names_extend_ti(1) padding_field_name_pad)

lemma toplevel_field_names_ti_typ_combine:
  "toplevel_field_names (ti_typ_combine t_b acc upd algn fn t) = toplevel_field_names t @ [fn]"
  by (simp add: ti_typ_combine_def toplevel_field_names_extend_ti)

lemma toplevel_field_names_no_padding_ti_typ_combine:
  "\<not> padding_field_name fn \<Longrightarrow>
  filter (Not o padding_field_name) (toplevel_field_names (ti_typ_combine t_b acc upd algn fn t)) =
    filter (Not o padding_field_name)  (toplevel_field_names t) @ [fn]"
  by (simp add: toplevel_field_names_ti_typ_combine toplevel_field_names_extend_ti)



lemma toplevel_field_names_no_padding_ti_typ_pad_combine:
  "\<not> padding_field_name fn \<Longrightarrow>
   filter (Not o padding_field_name) (toplevel_field_names (ti_typ_pad_combine t_b acc upd algn fn t)) =
       filter (Not o padding_field_name) (toplevel_field_names t) @ [fn]"
  by (simp add: ti_typ_pad_combine_def toplevel_field_names_ti_typ_combine toplevel_field_names_no_padding_ti_pad_combine Let_def)

lemma toplevel_field_names_ti_typ_pad_combine:
  "toplevel_field_names (ti_typ_pad_combine (t_b:: 'b itself) acc upd algn fn t) =
 toplevel_field_names t @ (
   if 0 < padup (max (2 ^ algn) (align_of TYPE('b::c_type))) (size_td t) then
     [foldl (@) ''!pad_'' (CompoundCTypes.field_names_list t), fn]
   else
     [fn])"
  by (simp add: ti_typ_pad_combine_def toplevel_field_names_ti_typ_combine toplevel_field_names_no_padding_ti_pad_combine Let_def
      toplevel_field_names_ti_pad_combine)

lemma toplevel_field_names_map_align: "toplevel_field_names (map_align n t) = toplevel_field_names t"
  by (cases t) (simp add: map_align_def)

lemma toplevel_field_names_no_padding_final_pad:
"filter (Not o padding_field_name) (toplevel_field_names  (final_pad n t))
  = filter (Not o padding_field_name) (toplevel_field_names t)"
  by (simp add: final_pad_def Let_def toplevel_field_names_map_align toplevel_field_names_no_padding_ti_pad_combine)


lemma toplevel_field_names_final_pad:
"(toplevel_field_names (final_pad n t))
  =
     toplevel_field_names t @ (
       if 0 < padup (2 ^ max n (align_td t)) (size_td t) then
         [foldl (@) ''!pad_'' (CompoundCTypes.field_names_list t)]
       else [])"
  by (simp add: final_pad_def Let_def toplevel_field_names_map_align toplevel_field_names_ti_pad_combine)

lemmas toplevel_field_names_no_padding_combinator_simps =
  toplevel_field_names_no_padding_empty_typ_info
  toplevel_field_names_no_padding_final_pad
  toplevel_field_names_no_padding_ti_typ_pad_combine
  toplevel_field_names_no_padding_ti_typ_combine

lemmas toplevel_field_names_combinator_simps =
  toplevel_field_names_empty_typ_info
  toplevel_field_names_final_pad
  toplevel_field_names_ti_typ_pad_combine
  toplevel_field_names_ti_typ_combine

lemma fold_filter_out_id:
  assumes filter_out_id: "\<And>i v. i < length xs \<Longrightarrow> \<not> P (xs ! i) \<Longrightarrow> f (xs!i) v = v"
  shows"fold f xs = fold f (filter P xs)"
  using filter_out_id
  apply (induct xs)
   apply simp
  apply (clarsimp simp add: comp_def fun_eq_iff, safe)
   apply (metis Suc_mono nth_Cons_Suc)
  by (metis not_less_eq nth_Cons_0 nth_Cons_Suc zero_less_Suc)

context xmem_type
begin

lemma xmem_type_toplevel_field_names_sum_list_size:
assumes aggregate: "aggregate (typ_info_t TYPE('a))"
shows "sum_list
         (map (\<lambda>f. size_td (fst (the (field_lookup (typ_info_t TYPE('a)) [f] n))))
         (toplevel_field_names (typ_info_t TYPE('a)))) =
      size_of TYPE('a)"
  using toplevel_field_names_sum_list_size(1) [OF aggregate wf_desc] by (simp add: size_of_def)

lemma xmem_type_toplevel_field_names_sum_list_offset:
  assumes aggregate: "aggregate (typ_info_t TYPE('a))"
  assumes i_bound: "i < length (toplevel_field_names (typ_info_t TYPE('a)))"
shows
"sum_list (map (\<lambda>i. size_td (fst (the (field_lookup (typ_info_t TYPE('a))
                    [(toplevel_field_names (typ_info_t TYPE('a))) ! i] 0))))
          [0..<i]) =
  (snd (the (field_lookup (typ_info_t TYPE('a)) [(toplevel_field_names (typ_info_t TYPE('a))) ! i] 0)))"
  using toplevel_field_names_sum_list_offset(1) [OF aggregate wf_desc i_bound, where n=0]
  by simp


lemma xmem_type_toplevel_field_names_field_lookup:
assumes f:  "f \<in> set (toplevel_field_names (typ_info_t TYPE('a)))"
shows "\<exists>s n. field_lookup (typ_info_t TYPE('a)) [f] 0 = Some (s, n)"
  using toplevel_field_names_field_lookup(1) [OF f wf_desc, of 0] by simp

lemma (in c_type) field_lookup_typ_uinfo_t_Some:
"field_lookup (typ_info_t TYPE('a)) f m = Some (s, n) \<Longrightarrow>
field_lookup (typ_uinfo_t TYPE('a)) f m = Some (export_uinfo s, n)"
  by (simp add: typ_uinfo_t_def field_lookup_export_uinfo_Some)

lemma toplevel_field_names_field_lookup_offset_conv:
  assumes f: "f \<in> set (toplevel_field_names (typ_info_t TYPE('a)))"
  shows "snd (the (field_lookup (typ_uinfo_t TYPE('a)) [f] 0)) =
          snd (the (field_lookup (typ_info_t TYPE('a)) [f] 0))"
  using xmem_type_toplevel_field_names_field_lookup [OF f]
  by (auto simp add: field_lookup_typ_uinfo_t_Some )


lemma heap_update_list_fold_toplevel_field_names:
  fixes p::"'a ptr"
  assumes aggregate: "aggregate (typ_info_t TYPE('a))"
  assumes cgrd: "c_guard p"
  shows
"heap_update_list (ptr_val p) (to_bytes x (heap_list h (size_of TYPE('a)) (ptr_val p))) h =
  fold
   (\<lambda>f h. heap_update_list (&(p\<rightarrow>[f]))
            (access_ti
              (fst (the (field_lookup (typ_info_t TYPE('a)) [f] 0)))
              x
              (heap_list h (size_td (fst (the (field_lookup (typ_info_t TYPE('a)) [f] 0)))) (&(p\<rightarrow>[f]))))
             h)
   (toplevel_field_names (typ_info_t TYPE('a))) h" (is "?LHS = fold ?F ?fs h")
proof -

  define fld::"nat \<Rightarrow> field_name" where
    "fld = (\<lambda>i. toplevel_field_names (typ_info_t TYPE('a)) ! i)"
  define sz:: "nat \<Rightarrow> nat" where
    "sz = (\<lambda>i. size_td (fst (the (field_lookup (typ_info_t TYPE('a)) [fld i] 0))))"
  define off:: "nat \<Rightarrow> nat" where
    "off = (\<lambda>i. snd (the (field_lookup (typ_info_t TYPE('a)) [fld i] 0)))"
  define v:: "nat \<Rightarrow> byte list \<Rightarrow> byte list" where
    "v = (\<lambda>i. (access_ti
                (fst (the (field_lookup (typ_info_t TYPE('a)) [fld i] 0)))
                x))"

  have lbs: "length (to_bytes x (heap_list h (size_of TYPE('a)) (ptr_val p))) = size_of TYPE('a)"
    by (simp add: local.lense.access_result_size to_bytes_def)
  {
    fix i::nat
    assume bound: " i < length (toplevel_field_names (typ_info_t TYPE('a)))"
    hence "toplevel_field_names (typ_info_t TYPE('a)) ! i \<in> set (toplevel_field_names (typ_info_t TYPE('a)))"
      by simp
    from toplevel_field_names_field_lookup_offset_conv [OF this]

    have "snd (the (field_lookup (typ_uinfo_t TYPE('a))
                [toplevel_field_names (typ_info_t TYPE('a)) ! i] 0)) =
          snd (the (field_lookup (typ_info_t TYPE('a))
                [toplevel_field_names (typ_info_t TYPE('a)) ! i] 0))" .
  } note field_lookup_conv = this

  have fs: "?fs = map fld [0..<length(toplevel_field_names (typ_info_t TYPE('a)))]"
    by (simp add: fld_def map_nth)

  from c_guard_no_wrap' [OF cgrd]
  have no_overflow: "unat (ptr_val p) + size_of TYPE('a) \<le> addr_card" .
  have fold_conv:
    "fold ?F ?fs h =
        fold
          (\<lambda>i h. heap_update_list (ptr_val p + word_of_nat (off i))
             (v i (heap_list h (sz i) (ptr_val p + word_of_nat (off i)))) h)
          [0..<length (toplevel_field_names (typ_info_t TYPE('a)))] h"
    apply (subst fs)
    apply (subst fold_map)
    apply (rule fold_cong [OF refl refl])
    apply (simp add: fld_def off_def sz_def v_def field_lvalue_def field_offset_def field_offset_untyped_def)
    apply (simp add: field_lookup_conv)
    done
  note partition= heap_update_list_fold_partition [where a= "ptr_val p" and sz=sz and off=off and v=v and h=h
       and bs = "to_bytes x (heap_list h (size_of TYPE('a)) (ptr_val p))" and
        m = "length (toplevel_field_names (typ_info_t TYPE('a)))"
      ]

  {
    fix i
    assume i_bound: "i < length (toplevel_field_names (typ_info_t TYPE('a)))"
    from i_bound
    have f: "toplevel_field_names (typ_info_t TYPE('a)) ! i \<in> set (toplevel_field_names (typ_info_t TYPE('a)))"
      by simp
    from toplevel_field_names_field_lookup(1)  [OF f, where m= 0, OF wf_desc]
    obtain s n where
      fl: "field_lookup (typ_info_t TYPE('a))
             [toplevel_field_names (typ_info_t TYPE('a)) ! i] 0 =
           Some (s, n)" by auto

    have lh: "length (heap_list h (size_of TYPE('a)) (ptr_val p)) = size_of TYPE('a)" by simp
    have "v i (take (sz i)
          (drop (off i)
            (heap_list h
              (length (to_bytes x (heap_list h (size_of TYPE('a)) (ptr_val p))))
              (ptr_val p)))) =
          take (sz i) (drop (off i) (to_bytes x (heap_list h (size_of TYPE('a)) (ptr_val p))))"
      apply (simp add: off_def sz_def v_def fld_def lbs)
      apply (simp add: fl)
      using mem_type_field_lookup_access_ti_take_drop [OF fl lh, where v=x ]
      apply (simp add: to_bytes_def)
      done

  } note v_focus = this
  show ?thesis
    apply (subst fold_conv)
    apply (rule partition)
    subgoal
      using no_overflow
      by (simp add: local.lense.access_result_size to_bytes_def)
    subgoal
      apply (subst xmem_type_partition_toplevel_field_names [OF aggregate lbs, symmetric])
      apply (subst fs)
      apply (subst map_map)
      apply (rule arg_cong [where f=concat])
      apply (rule map_cong [OF refl])
      apply (simp add: fld_def off_def sz_def)
      done
    subgoal
      apply (subst lbs)
      apply (subst xmem_type_toplevel_field_names_sum_list_size [OF aggregate, symmetric])
      apply (simp add: sz_def)
      apply (subst fs)
      apply (simp add: fld_def comp_def)
      done
    subgoal for i
      apply (simp add: off_def sz_def)
      apply (simp add: fld_def)
      using xmem_type_toplevel_field_names_sum_list_offset [OF aggregate, where i = i]
      apply simp
      done
    subgoal for i
      by (rule v_focus)
    done
qed

lemma heap_update_list_padding_fold_toplevel_field_names:
  fixes p::"'a ptr"
  assumes aggregate: "aggregate (typ_info_t TYPE('a))"
  assumes cgrd: "c_guard p"
  assumes lbs: "length bs = size_of TYPE('a)"
  shows
"heap_update_list (ptr_val p) (to_bytes x bs) h =
  fold
   (\<lambda>f h. heap_update_list (&(p\<rightarrow>[f]))
            (access_ti
              (fst (the (field_lookup (typ_info_t TYPE('a)) [f] 0)))
              x
              (take (size_td (fst (the (field_lookup (typ_info_t TYPE('a)) [f] 0))))
                (drop ((snd (the (field_lookup (typ_info_t TYPE('a)) [f] 0)))) bs)))
             h)
   (toplevel_field_names (typ_info_t TYPE('a))) h" (is "?LHS = fold ?F ?fs h")
proof -

  define fld::"nat \<Rightarrow> field_name" where
    "fld = (\<lambda>i. toplevel_field_names (typ_info_t TYPE('a)) ! i)"
  define sz:: "nat \<Rightarrow> nat" where
    "sz = (\<lambda>i. size_td (fst (the (field_lookup (typ_info_t TYPE('a)) [fld i] 0))))"
  define off:: "nat \<Rightarrow> nat" where
    "off = (\<lambda>i. snd (the (field_lookup (typ_info_t TYPE('a)) [fld i] 0)))"
  define v:: "nat \<Rightarrow> byte list \<Rightarrow> byte list" where
    "v = (\<lambda>i. (access_ti
                (fst (the (field_lookup (typ_info_t TYPE('a)) [fld i] 0)))
                x))"

  have lbs': "length (to_bytes x bs) = size_of TYPE('a)"
    by (simp add: local.lense.access_result_size to_bytes_def)
  {
    fix i::nat
    assume bound: " i < length (toplevel_field_names (typ_info_t TYPE('a)))"
    hence "toplevel_field_names (typ_info_t TYPE('a)) ! i \<in> set (toplevel_field_names (typ_info_t TYPE('a)))"
      by simp
    from toplevel_field_names_field_lookup_offset_conv [OF this]

    have "snd (the (field_lookup (typ_uinfo_t TYPE('a))
                [toplevel_field_names (typ_info_t TYPE('a)) ! i] 0)) =
          snd (the (field_lookup (typ_info_t TYPE('a))
                [toplevel_field_names (typ_info_t TYPE('a)) ! i] 0))" .
  } note field_lookup_conv = this

  have fs: "?fs = map fld [0..<length(toplevel_field_names (typ_info_t TYPE('a)))]"
    by (simp add: fld_def map_nth)

  from c_guard_no_wrap' [OF cgrd]
  have no_overflow: "unat (ptr_val p) + size_of TYPE('a) \<le> addr_card" .
  have fold_conv:
    "fold ?F ?fs h =
        fold
          (\<lambda>i h. heap_update_list (ptr_val p + word_of_nat (off i))
             (v i (take (sz i) (drop (off i) bs))) h)
          [0..<length (toplevel_field_names (typ_info_t TYPE('a)))] h"
    apply (subst fs)
    apply (subst fold_map)
    apply (rule fold_cong [OF refl refl])
    apply (simp add: fld_def off_def sz_def v_def field_lvalue_def field_offset_def field_offset_untyped_def)
    apply (simp add: field_lookup_conv)
    done

  note partition= heap_update_list_padding_fold_partition [where a= "ptr_val p" and sz=sz and off=off and v=v and h=h
       and bs = "to_bytes x bs" and pbs = bs and
        m = "length (toplevel_field_names (typ_info_t TYPE('a)))"
      ]

  {
    fix i
    assume i_bound: "i < length (toplevel_field_names (typ_info_t TYPE('a)))"
    from i_bound
    have f: "toplevel_field_names (typ_info_t TYPE('a)) ! i \<in> set (toplevel_field_names (typ_info_t TYPE('a)))"
      by simp
    from toplevel_field_names_field_lookup(1)  [OF f, where m= 0, OF wf_desc]
    obtain s n where
      fl: "field_lookup (typ_info_t TYPE('a))
             [toplevel_field_names (typ_info_t TYPE('a)) ! i] 0 =
           Some (s, n)" by auto

    have lh: "length (heap_list h (size_of TYPE('a)) (ptr_val p)) = size_of TYPE('a)" by simp
    have "v i (take (sz i) (drop (off i) bs)) =
           take (sz i) (drop (off i) (to_bytes x bs))"
      apply (simp add: off_def sz_def v_def fld_def lbs)
      apply (simp add: fl)
      using mem_type_field_lookup_access_ti_take_drop [OF fl lbs, where v=x ]
      apply (simp add: to_bytes_def)
      done

  } note v_focus = this
  show ?thesis
    apply (subst fold_conv)
    apply (rule partition)
    subgoal
      using no_overflow
      by (simp add: local.lense.access_result_size to_bytes_def)
    subgoal
      apply (subst xmem_type_partition_toplevel_field_names [OF aggregate lbs', symmetric])
      apply (subst fs)
      apply (subst map_map)
      apply (rule arg_cong [where f=concat])
      apply (rule map_cong [OF refl])
      apply (simp add: fld_def off_def sz_def)
      done
    subgoal
      apply (subst lbs')
      apply (subst xmem_type_toplevel_field_names_sum_list_size [OF aggregate, symmetric])
      apply (simp add: sz_def)
      apply (subst fs)
      apply (simp add: fld_def comp_def)
      done
    subgoal
      apply (subst xmem_type_partition_toplevel_field_names [OF aggregate lbs, symmetric])
      apply (subst fs)
      apply (subst map_map)
      apply (rule arg_cong [where f=concat])
      apply (rule map_cong [OF refl])
      apply (simp add: fld_def off_def sz_def)
      done
    subgoal
      apply (subst lbs)
      apply (subst xmem_type_toplevel_field_names_sum_list_size [OF aggregate, symmetric])
      apply (simp add: sz_def)
      apply (subst fs)
      apply (simp add: fld_def comp_def)
      done
    subgoal for i
      apply (simp add: off_def sz_def)
      apply (simp add: fld_def)
      using xmem_type_toplevel_field_names_sum_list_offset [OF aggregate, where i = i]
      apply simp
      done
    subgoal for i
      by (rule v_focus)
    done
qed

lemma heap_update_fold_toplevel_field_names:
  fixes p::"'a ptr"
  assumes aggregate: "aggregate (typ_info_t TYPE('a))"
  assumes cgrd: "c_guard p"
  shows
"heap_update p x h =
  fold
   (\<lambda>f h. heap_update_list (&(p\<rightarrow>[f]))
            (access_ti
              (fst (the (field_lookup (typ_info_t TYPE('a)) [f] 0)))
              x
              (heap_list h (size_td (fst (the (field_lookup (typ_info_t TYPE('a)) [f] 0)))) (&(p\<rightarrow>[f]))))
             h)
   (toplevel_field_names (typ_info_t TYPE('a))) h" (is "?LHS = fold ?F ?fs h")
  using heap_update_list_fold_toplevel_field_names [OF aggregate cgrd]
  by (simp only: heap_update_def)

lemma heap_update_padding_fold_toplevel_field_names:
  fixes p::"'a ptr"
  assumes aggregate: "aggregate (typ_info_t TYPE('a))"
  assumes cgrd: "c_guard p"
  assumes lbs: "length bs = size_of TYPE('a)"
  shows
"heap_update_padding p x bs h =
  fold
   (\<lambda>f h. heap_update_list (&(p\<rightarrow>[f]))
            (access_ti
              (fst (the (field_lookup (typ_info_t TYPE('a)) [f] 0)))
              x
              (take (size_td (fst (the (field_lookup (typ_info_t TYPE('a)) [f] 0))))
                (drop ((snd (the (field_lookup (typ_info_t TYPE('a)) [f] 0)))) bs)))
             h)
   (toplevel_field_names (typ_info_t TYPE('a))) h" (is "?LHS = fold ?F ?fs h")
  using heap_update_list_padding_fold_toplevel_field_names [OF aggregate cgrd lbs]
  by (simp only: heap_update_padding_def)

lemma heap_update_fold_toplevel_field_names_no_padding:
  fixes p::"'a ptr"
  assumes aggregate: "aggregate (typ_info_t TYPE('a))"
  assumes cgrd: "c_guard p"
  shows
"heap_update p x h =
  fold
   (\<lambda>f h. heap_update_list (&(p\<rightarrow>[f]))
            (access_ti
              (fst (the (field_lookup (typ_info_t TYPE('a)) [f] 0)))
              x
              (heap_list h (size_td (fst (the (field_lookup (typ_info_t TYPE('a)) [f] 0)))) (&(p\<rightarrow>[f]))))
             h)
   (filter (Not o padding_field_name) (toplevel_field_names (typ_info_t TYPE('a)))) h" (is "?LHS = fold ?F ?filter_fs h")
proof -

  { fix i
    fix h
    assume i_bound: "i < length (toplevel_field_names (typ_info_t TYPE('a)))"
    assume "\<not> (Not \<circ> padding_field_name)
               (toplevel_field_names (typ_info_t TYPE('a)) ! i)"
    hence padding: "padding_field_name (toplevel_field_names (typ_info_t TYPE('a)) ! i)"
      by simp
    from i_bound obtain m s where
        fl: "field_lookup (typ_info_t TYPE('a))
               [(toplevel_field_names (typ_info_t TYPE('a)) ! i)] 0 = Some (s, m)"
      by (meson nth_mem xmem_type_toplevel_field_names_field_lookup)


    from field_lookup_padding_field_name(1) [OF fl padding wf_padding]
    have is_padding_tag: "is_padding_tag s" .

    have "?F (toplevel_field_names (typ_info_t TYPE('a)) ! i) h = h"
      apply (simp add: fl)
      using is_padding_tag
        by (clarsimp simp add: is_padding_tag_def padding_tag_def padding_desc_def heap_update_list_id')
  } note pad = this

  have "fold ?F ?filter_fs = fold ?F (toplevel_field_names (typ_info_t TYPE('a)))"
    apply (rule fold_filter_out_id [symmetric])
    by (rule pad)
  with heap_update_fold_toplevel_field_names [OF aggregate cgrd, where x=x and h=h]
  show ?thesis
    by simp
qed

lemma heap_list_concat_toplevel_field_names:
  fixes p::"'a ptr"
  assumes aggregate: "aggregate (typ_info_t TYPE('a))"
  assumes cgrd: "c_guard p"
  shows
   "heap_list h (size_of TYPE('a)) (ptr_val p) =
      concat (map (\<lambda>f. heap_list h (size_td (fst (the (field_lookup (typ_info_t TYPE('a)) [f] 0)))) (&(p\<rightarrow>[f])))
         (toplevel_field_names (typ_info_t TYPE('a))))" (is "?LHS = concat (map ?F ?fs)")
proof -
  define fld::"nat \<Rightarrow> field_name" where
    "fld = (\<lambda>i. toplevel_field_names (typ_info_t TYPE('a)) ! i)"
  define sz:: "nat \<Rightarrow> nat" where
    "sz = (\<lambda>i. size_td (fst (the (field_lookup (typ_info_t TYPE('a)) [fld i] 0))))"
  define off:: "nat \<Rightarrow> nat" where
    "off = (\<lambda>i. snd (the (field_lookup (typ_info_t TYPE('a)) [fld i] 0)))"

  have fs: "?fs = map fld [0..<length(toplevel_field_names (typ_info_t TYPE('a)))]"
    by (simp add: fld_def map_nth)
  from c_guard_no_wrap' [OF cgrd]
  have no_overflow: "unat (ptr_val p) + size_of TYPE('a) \<le> addr_card" .

  have concat_conv:
   "concat (map ?F ?fs) =
    concat (map (\<lambda>i. (heap_list h (sz i) (ptr_val p + word_of_nat (off i))))
      [0..<length (toplevel_field_names (typ_info_t TYPE('a)))])"
    apply (subst fs)
    apply (subst list.map_comp)
    apply (rule arg_cong [where f=concat])
    apply (rule map_cong [OF refl])
    apply (simp add: fld_def off_def sz_def field_lvalue_def field_offset_def field_offset_untyped_def)
    by (simp add: toplevel_field_names_field_lookup_offset_conv)

  note partition =  heap_list_map_partition [where a= "ptr_val p", where sz=sz and off=off and n="size_of TYPE('a)" and
    m = "length (toplevel_field_names (typ_info_t TYPE('a)))", OF no_overflow]
  show ?thesis
    apply (subst concat_conv)
    apply (rule partition)
    subgoal
      apply (subst xmem_type_toplevel_field_names_sum_list_size [OF aggregate, symmetric])
      apply (simp add: sz_def)
      apply (subst fs)
      apply (simp add: fld_def comp_def)
      done
    subgoal for i
      apply (simp add: off_def sz_def)
      apply (simp add: fld_def)
      using xmem_type_toplevel_field_names_sum_list_offset [OF aggregate, where i = i]
      apply simp
      done
    done
qed


lemma h_val_concat_toplevel_field_names:
  fixes p::"'a ptr"
  assumes aggregate: "aggregate (typ_info_t TYPE('a))"
  assumes cgrd: "c_guard p"
  shows
   "h_val h p =
      from_bytes
         (concat (map (\<lambda>f. heap_list h (size_td (fst (the (field_lookup (typ_info_t TYPE('a)) [f] 0)))) (&(p\<rightarrow>[f])))
         (toplevel_field_names (typ_info_t TYPE('a)))))"
  using heap_list_concat_toplevel_field_names [OF aggregate cgrd]
  by (simp add: h_val_def)

end



lemma set_field_names_u_all_field_names_conv:
  "set (field_names_u (typ_uinfo_t TYPE('a::mem_type)) t) =
    {f.  f \<in> set (all_field_names (typ_info_t TYPE('a))) \<and>
         (\<exists>s. field_ti TYPE('a) f = Some s \<and> export_uinfo s = t)}"
  apply standard
  subgoal
    apply (clarsimp simp add: typ_uinfo_t_def)
    apply (rule conjI)
     apply (metis (mono_tags, lifting) all_field_names_export_uinfo field_names_subset_all_field_names(1) in_mono)
    by (metis field_lookup_field_ti field_names_Some2(1) field_names_u_field_names_export_uinfo_conv(1) wf_desc)
  subgoal
    apply clarsimp
    by (metis all_field_names_exists_field_names_u(1) all_field_names_export_uinfo
        field_lookup_field_ti field_names_Some2(1) field_names_u_field_names_export_uinfo_conv(1) fold_typ_uinfo_t option.inject wf_desc)
  done

lemma field_names_u_all_field_names_conv:
  "field_names_u (typ_uinfo_t TYPE('a::mem_type)) t =
    filter (\<lambda>f. (\<exists>s. field_ti TYPE('a) f = Some s \<and> export_uinfo s = t))
     (all_field_names (typ_info_t TYPE('a)))"
  using field_names_u_filter_all_field_names_conv(1)
  by (smt (verit) all_field_names_exists_field_names_u(1) all_field_names_export_uinfo field_lookup_field_ti
      field_lookup_uinfo_Some_rev field_ti_def filter_same_eq fold_typ_uinfo_t
      mem_Collect_eq option.sel set_field_names_u_all_field_names_conv set_filter wf_desc_typ_tag)

lemma set_field_names_all_field_names_conv:
  "set (field_names (typ_info_t TYPE('a::mem_type)) t) =
    {f.  f \<in> set (all_field_names (typ_info_t TYPE('a))) \<and>
         (\<exists>s. field_ti TYPE('a) f = Some s \<and> export_uinfo s = t)}"
  using set_field_names_u_all_field_names_conv [of t]
  unfolding typ_uinfo_t_def
  by (simp add: field_names_u_field_names_export_uinfo_conv(1))

lemma field_names_all_field_names_conv:
  "field_names (typ_info_t TYPE('a::mem_type)) t =
    filter (\<lambda>f. \<exists>s. field_ti TYPE('a) f = Some s \<and> export_uinfo s = t) (all_field_names (typ_info_t TYPE('a)))"
  using field_names_u_all_field_names_conv [of t]
  unfolding typ_uinfo_t_def
  by (simp add: field_names_u_field_names_export_uinfo_conv(1))

lemma field_lookup_qualified_padding_field_name:
  fixes
  t:: "('a, 'b) typ_info " and
  st :: "('a, 'b) typ_info_struct" and
  ts :: "('a, 'b) typ_info_tuple list" and
  x :: "('a, 'b) typ_info_tuple"
shows
"field_lookup t f n = Some (s, m) \<Longrightarrow> qualified_padding_field_name f \<Longrightarrow> wf_padding t \<Longrightarrow>
   is_padding_tag s"
"field_lookup_struct st f n = Some (s, m) \<Longrightarrow> qualified_padding_field_name f \<Longrightarrow> wf_padding_struct st \<Longrightarrow>
   is_padding_tag s"
"field_lookup_list ts f n = Some (s, m) \<Longrightarrow> qualified_padding_field_name f \<Longrightarrow> wf_padding_list ts \<Longrightarrow>
   is_padding_tag s"
"field_lookup_tuple x f n = Some (s, m) \<Longrightarrow> qualified_padding_field_name f \<Longrightarrow> wf_padding_tuple x \<Longrightarrow>
   is_padding_tag s"
proof (induct t and st and ts and x arbitrary: f n m and f n m and f n m and f n m)
  case (TypDesc nat typ_struct list)
then show ?case by (auto split: if_split_asm option.splits)
next
case (TypScalar nat1 nat2 a)
  then show ?case by simp
next
  case (TypAggregate list)
  then show ?case by auto
next
case Nil_typ_desc
then show ?case by simp
next
  case (Cons_typ_desc dt_tuple list)
then show ?case by (auto split: if_split_asm option.splits)
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case
    apply clarsimp
    by (metis field_lookup_empty last_tl list.exhaust_sel option.distinct(1)
        option.inject prod.inject qualified_pading_field_name_cons qualified_pading_field_name_single)
qed


lemma all_field_names_empty_typ_info [simp]: "all_field_names (empty_typ_info algn n) = [[]]"
  by (simp add: empty_typ_info_def)

lemma all_field_names_no_padding_empty_typ_info [simp]:
  "filter (Not o qualified_padding_field_name) (all_field_names (empty_typ_info algn n)) = [[]]"
  by (simp)

lemma all_field_names_list_append [simp]:
  "all_field_names_list (xs @ ys) = all_field_names_list xs @ all_field_names_list ys"
  by (induct xs) auto

lemma all_field_names_extend_ti:
  fixes
  t :: "'a xtyp_info" and
  st :: "'a xtyp_info_struct" and
  ts :: "'a xtyp_info_tuple list" and
  x :: "'a xtyp_info_tuple"
  shows
  "all_field_names (extend_ti t s n fn d) = all_field_names t @ (map ((#) fn) (all_field_names s))"
  "all_field_names_struct (extend_ti_struct st s fn d) = all_field_names_struct st @ (map ((#) fn) (all_field_names s))"
  "all_field_names_list ts = all_field_names_list ts"
  "all_field_names_tuple x = all_field_names_tuple x"
     by (induct t and st and ts and x) auto

lemma all_field_names_adjust_ti':
  fixes
  t :: "'a xtyp_info" and
  st :: "'a xtyp_info_struct" and
  ts :: "'a xtyp_info_tuple list" and
  x :: "'a xtyp_info_tuple"
  shows
"all_field_names (map_td (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) t) =
  all_field_names t"
"all_field_names_struct (map_td_struct (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) st) =
  all_field_names_struct st"
"all_field_names_list (map_td_list (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) ts) =
  all_field_names_list ts"
"all_field_names_tuple (map_td_tuple (\<lambda>n algn. update_desc acc upd) (update_desc acc upd) x) =
  all_field_names_tuple x"
  by  (induct t and st and ts and x) (auto)

lemma all_field_names_adjust_ti[simp]:
  "all_field_names (adjust_ti t acc upd) = all_field_names t"
  by (simp add: all_field_names_adjust_ti' adjust_ti_def)

lemma all_field_names_no_padding_ti_pad_combine:
  "filter (Not o qualified_padding_field_name) (all_field_names (ti_pad_combine n t)) =
       filter (Not o qualified_padding_field_name) (all_field_names t)"
  by (simp add: ti_pad_combine_def Let_def  all_field_names_extend_ti(1) padding_field_name_pad)

lemma all_field_names_ti_typ_combine:
  "all_field_names (ti_typ_combine (t_b::'b::c_type itself) acc upd algn fn t) =
    all_field_names t @  (map ((#) fn) (all_field_names (typ_info_t TYPE('b))))"
  by (simp add: ti_typ_combine_def all_field_names_extend_ti)

lemma all_field_names_no_padding_ti_typ_combine:
  assumes not_padding: "\<not> padding_field_name fn"
  shows "filter (Not o qualified_padding_field_name) (all_field_names (ti_typ_combine (t_b::'b::c_type itself) acc upd algn fn t)) =
    filter (Not o qualified_padding_field_name)  (all_field_names t) @
    (map ((#) fn) (filter (Not o qualified_padding_field_name) (all_field_names (typ_info_t TYPE('b)))))"
proof -
  from not_padding have eq: "Not \<circ> qualified_padding_field_name \<circ> (#) fn = Not \<circ> qualified_padding_field_name"
    apply -
    apply (rule ext)
    apply (auto simp add: neq_Nil_conv)
    done
  from not_padding show ?thesis
    apply (simp add: all_field_names_ti_typ_combine all_field_names_extend_ti)
    apply (simp add: filter_map eq)
    done
qed

lemma all_field_names_no_padding_ti_typ_pad_combine:
  assumes not_padding: "\<not> padding_field_name fn"
  shows "filter (Not o qualified_padding_field_name) (all_field_names (ti_typ_pad_combine (t_b::'b::c_type itself) acc upd algn fn t)) =
    filter (Not o qualified_padding_field_name)  (all_field_names t) @
    (map ((#) fn) (filter (Not o qualified_padding_field_name) (all_field_names (typ_info_t TYPE('b)))))"
  by (simp add: ti_typ_pad_combine_def Let_def
      all_field_names_no_padding_ti_pad_combine all_field_names_no_padding_ti_typ_combine [OF not_padding])

lemma all_field_names_map_align[simp]: "all_field_names (map_align n t) = all_field_names t"
  by (cases t) (simp add: map_align_def)

lemma all_field_names_no_padding_final_pad:
"filter (Not o qualified_padding_field_name) (all_field_names  (final_pad n t))
  = filter (Not o qualified_padding_field_name) (all_field_names t)"
  by (simp add: final_pad_def Let_def all_field_names_no_padding_ti_pad_combine)

lemmas all_field_names_filter_no_padding_combinator_simps =
  all_field_names_no_padding_empty_typ_info
  all_field_names_no_padding_final_pad
  all_field_names_no_padding_ti_typ_pad_combine
  all_field_names_no_padding_ti_typ_combine


lemma all_field_names_array_tag_n:  "all_field_names ((array_tag_n n)::('a::c_type,'b::finite) array xtyp_info) =
   [] #
   concat (map (\<lambda>i. (map ((#) (replicate i CHR ''1'')) (all_field_names (typ_info_t TYPE('a))))) [0..<n]) "
  apply (induct n)
   apply (simp add: atn_base)
  apply (auto simp add: atn_rec all_field_names_ti_typ_combine)
  done

lemma all_field_names_array:
  "all_field_names (typ_info_t TYPE('a::c_type['b::finite])) =
     [] #
     concat (map (\<lambda>i. (map ((#) (replicate i CHR ''1'')) (all_field_names (typ_info_t TYPE('a))))) [0..<CARD('b)])"
  by (simp add: typ_info_array array_tag_def all_field_names_array_tag_n)

lemma not_padding_field_name_replicate_1[simp]: "padding_field_name (replicate n CHR ''1'') = False"
  by (cases n) auto

lemma non_empty_not_padding_field_conv: "(x \<noteq> [] \<longrightarrow> \<not> padding_field_name (last x)) \<longleftrightarrow> \<not> qualified_padding_field_name x"
  by (cases x) auto

named_theorems all_field_names_no_padding and set_all_field_names_no_padding

definition all_field_names_no_padding :: "('a, 'b) typ_desc \<Rightarrow> qualified_field_name list"
  where
  "all_field_names_no_padding t = filter (Not o qualified_padding_field_name) (all_field_names t)"


lemma all_field_names_no_padding_combinator_simps:
  "all_field_names_no_padding (empty_typ_info algn nm) = [[]]"
  "all_field_names_no_padding (final_pad n t) = all_field_names_no_padding t"
  "\<not> padding_field_name fn \<Longrightarrow>
  all_field_names_no_padding (ti_typ_pad_combine  (t_b::'b::c_type itself) acc upd algn fn t) =
    all_field_names_no_padding t @
    map ((#) fn)
     (all_field_names_no_padding  (typ_info_t TYPE('b::c_type)))"
  "\<not> padding_field_name fn \<Longrightarrow>
  all_field_names_no_padding (ti_typ_combine  (t_b::'b::c_type itself) acc upd algn fn t) =
  all_field_names_no_padding  t @
  map ((#) fn)
   (all_field_names_no_padding  (typ_info_t TYPE('b::c_type)))"
  by (simp_all add: all_field_names_no_padding_def all_field_names_filter_no_padding_combinator_simps)

lemma all_field_names_filter_no_padding_array:
 "filter (Not o qualified_padding_field_name) (all_field_names (typ_info_t TYPE('a::c_type['b::finite]))) =
   [] #
   concat (map (\<lambda>i. (map ((#) (replicate i CHR ''1''))
     (filter (Not o qualified_padding_field_name) (all_field_names (typ_info_t TYPE('a)))))) [0..<CARD('b)])"
  apply (simp add: all_field_names_array)
  apply (simp add: filter_concat)
  apply (simp add: comp_def filter_map add: non_empty_not_padding_field_conv )
  done

lemma all_field_names_no_padding_array[all_field_names_no_padding]:
 "all_field_names_no_padding (typ_info_t TYPE('a::c_type['b::finite])) =
   [] #
   concat (map (\<lambda>i. (map ((#) (replicate i CHR ''1''))
     (all_field_names_no_padding (typ_info_t TYPE('a))))) [0..<CARD('b)])"
  by (simp add: all_field_names_no_padding_def all_field_names_filter_no_padding_array)

lemma set_all_field_names_no_padding_array[set_all_field_names_no_padding]:
 "set (all_field_names_no_padding (typ_info_t TYPE('a::c_type['b::finite]))) =
  insert []
     (\<Union>x\<in>{0..<CARD('b)}.
         (#) (replicate x CHR ''1'') `
         set (all_field_names_no_padding (typ_info_t TYPE('a))))"

  by (simp add: all_field_names_no_padding_array)

lemma sub_typ_trans: "t \<le>\<^sub>\<tau> s \<Longrightarrow> s \<le>\<^sub>\<tau> w \<Longrightarrow> t \<le>\<^sub>\<tau> w"
  by (simp add: sub_typ_def)

lemma sub_typ_trans_rev: "s \<le>\<^sub>\<tau> w  \<Longrightarrow> t \<le>\<^sub>\<tau> s  \<Longrightarrow> t \<le>\<^sub>\<tau> w"
  by (simp add: sub_typ_def)



lemma element_typ_le_array_typ: "typ_uinfo_t TYPE('a::mem_type) \<le> typ_uinfo_t TYPE('a['b::finite])"
proof -
  have "0 < CARD('b)" by simp
  from field_lookup_array [OF this, of 0, simplified]
  have "field_lookup (typ_info_t TYPE('a['b])) [[]] 0 =
    Some (adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. x.[0]) (\<lambda>x f. Arrays.update f 0 x), 0)" .
  from td_set_field_lookupD [OF this]
  have "(adjust_ti (typ_info_t TYPE('a)) (\<lambda>x. x.[0]) (\<lambda>x f. Arrays.update f 0 x), 0)
    \<in> td_set (typ_info_t TYPE('a['b])) 0".
  from td_set_export_uinfoD [OF this]
  show ?thesis
    by (auto simp add: export_uinfo_adjust_ti typ_uinfo_t_def typ_tag_le_def)
qed

lemma element_typ_subtyp_array_typ: "TYPE ('a::mem_type) \<le>\<^sub>\<tau> TYPE('a['b::finite])"
  by (simp add: sub_typ_def element_typ_le_array_typ)

lemma field_lookup_sub_typ:
assumes fl: "field_lookup (typ_info_t TYPE('a::c_type)) f 0 = Some (s, m)"
assumes match: "export_uinfo s = export_uinfo (typ_info_t TYPE('b::c_type))"
shows "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  using  match td_set_export_uinfoD [OF td_set_field_lookupD [OF fl]]
  by (auto simp add: sub_typ_def typ_tag_le_def typ_uinfo_t_def)

lemma field_lookup_sub_typ':
  assumes fl: "field_lookup (typ_info_t TYPE('a::c_type)) f 0 \<equiv> Some (adjust_ti (typ_info_t TYPE('b::mem_type)) acc upd, n)"
  assumes fg_cons: "fg_cons acc upd"
shows "TYPE('b) \<le>\<^sub>\<tau> TYPE('a)"
  apply (rule field_lookup_sub_typ [of f])
   apply (simp add: fl)
  using fg_cons
  by (simp add: export_uinfo_adjust_ti)

lemma all_field_names_no_padding_word[all_field_names_no_padding]:
  "all_field_names_no_padding (typ_info_t (TYPE('a::len8 word))) = [[]]"
  by (simp add: all_field_names_no_padding_def)

lemma set_all_field_names_no_padding_word[set_all_field_names_no_padding]:
  "set (all_field_names_no_padding (typ_info_t (TYPE('a::len8 word)))) = {[]}"
  by (simp add: all_field_names_no_padding_def)

lemma all_field_names_no_padding_ptr[all_field_names_no_padding]:
  "all_field_names_no_padding (typ_info_t (TYPE('a::c_type ptr))) = [[]]"
  by (simp add: all_field_names_no_padding_def)

lemma set_all_field_names_no_padding_ptr[set_all_field_names_no_padding]:
  "set (all_field_names_no_padding (typ_info_t (TYPE('a::c_type ptr)))) = {[]}"
  by (simp add: all_field_names_no_padding_def)


definition field_names_no_padding::"('a, 'b) typ_info \<Rightarrow>  typ_uinfo \<Rightarrow> qualified_field_name list"
  where "field_names_no_padding t s = filter (Not o qualified_padding_field_name) (field_names t s)"


lemma set_field_names_no_padding_all_field_names_no_padding_conv:
"set (field_names_no_padding (typ_info_t TYPE('a::mem_type)) t) =
 {f \<in> set (all_field_names_no_padding (typ_info_t TYPE('a))).
    \<exists>s n. field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n) \<and> export_uinfo s = t}"
  using set_field_names_all_field_names_conv [where 'a='a and t=t]
  by (auto simp add: field_ti_def all_field_names_no_padding_def field_names_no_padding_def split: option.split)

lemma field_names_no_padding_all_field_names_no_padding_conv:
"field_names_no_padding (typ_info_t TYPE('a::mem_type)) t =
 filter (\<lambda>f. \<exists>s n. field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n) \<and> export_uinfo s = t)
   (all_field_names_no_padding (typ_info_t TYPE('a)))"
  using field_names_all_field_names_conv [where 'a='a and t=t]
  by (auto simp add: field_ti_def all_field_names_no_padding_def field_names_no_padding_def intro: filter_same_eq split: option.split)

lemma subset_all_field_names_no_padding_all_field_names:
  "set (all_field_names_no_padding t) \<subseteq> set (all_field_names t)"
  by (simp add: all_field_names_no_padding_def)

lemma all_field_names_typ_uinfo_t_conv:
  "all_field_names (typ_info_t (TYPE('a::c_type))) = all_field_names (typ_uinfo_t (TYPE('a::c_type)))"
  by (simp add: all_field_names_export_uinfo typ_uinfo_t_def)

lemma all_field_names_no_padding_typ_uinfo_t_conv:
  "all_field_names_no_padding (typ_info_t (TYPE('a::c_type))) = all_field_names_no_padding (typ_uinfo_t (TYPE('a::c_type)))"
  by (simp add: all_field_names_no_padding_def all_field_names_typ_uinfo_t_conv)

lemma update_ti_to_bytes_p[simp]:
  "update_ti (typ_info_t TYPE('a::xmem_type)) (to_bytes_p (v::'a)) w = v"
  apply (subst field_lookup_update_ti_from_bytes_field_conv[OF
        field_lookup_empty , where xbs="replicate (size_of TYPE('a)) 0" and v=v])
  unfolding typ_uinfo_t_def apply (rule refl)
  apply (simp add: size_of_def)
  apply (simp add: to_bytes_p_def to_bytes_def)
  apply (subst field_lookup_update_ti_from_bytes_field_conv[symmetric, where vf=v,
        OF field_lookup_empty])
  apply (simp_all add: size_of_def typ_uinfo_t_def)
  apply (simp add: to_bytes_p_def to_bytes_def)
  apply (intro lense.update_access)
  done

context mem_type
begin

lemma mem_type_access_ti_super_update_bs:
  assumes fl: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, n)"
  assumes lbs: "length bs = size_of TYPE('a)"
  assumes lbs': "length bs' = size_td s"
  shows "access_ti (typ_info_t TYPE('a))
    (update_ti s (access_ti\<^sub>0 s w) v) (super_update_bs bs' bs n) =
    super_update_bs (access_ti s w bs') (access_ti (typ_info_t TYPE('a)) v bs) n"
proof -
  have "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s, 0 + n)" using fl by simp
  from access_ti_super_update_bs_of_wf(1)[OF this lbs' lbs[unfolded size_of_def]]
  show ?thesis by simp
qed

end

lemma update_ti_undefined[simp]:
  assumes "NO_MATCH undefined w" assumes bs: "length bs = size_of TYPE('a)"
  shows "update_ti (typ_info_t TYPE('a::xmem_type)) bs w =
    update_ti (typ_info_t TYPE('a)) bs undefined"
  by (simp add: bs size_of_def upd_rf update_ti_update_ti_t)


section \<open>\<open>heap_upd\<close> and \<open>heap_upd_list\<close>\<close>

section \<open>\<open>heap_upd\<close>\<close>

lemma heap_upd_id: "heap_upd (p::'a::xmem_type ptr) id = id"
  by (simp add: heap_upd_def fun_eq_iff xmem_type_class.heap_update_id)

lemma heap_upd_const: "heap_upd p (\<lambda>_. x) = heap_update p x"
  by (simp add: heap_upd_def[abs_def])

lemma heap_upd_comp: "heap_upd (p::'a::xmem_type ptr) (f \<circ> g) = heap_upd p f \<circ> heap_upd p g"
  by (simp add: heap_upd_def fun_eq_iff h_val_heap_update heap_update_collapse)

lemma hrs_mem_update_heap_upd:
  "hrs_mem_update (heap_upd p g) h = hrs_mem_update (heap_update p (g (h_val (hrs_mem h) p))) h"
  by (cases h) (simp add: hrs_mem_update_def heap_upd_def hrs_mem_def)

lemma heap_update_eq_heap_upd_list:
  fixes p :: "'a::mem_type ptr"
  shows "heap_update p x =
    heap_upd_list (size_of TYPE('a)) (ptr_val p) (access_ti (typ_info_t TYPE('a)) x)"
  by (simp add: heap_update_def fun_eq_iff heap_upd_list_def to_bytes_def)

lemma heap_upd_list_id[simp]: "heap_upd_list n p id = id"
  by (simp add: heap_upd_list_def fun_eq_iff heap_update_list_id')

lemma heap_upd_list_access_ti_typ_info_t[simp]:
  "sz = size_of TYPE('a) \<Longrightarrow>
    heap_upd_list sz p (access_ti (typ_info_t TYPE('a::xmem_type)) v) =
    heap_update (PTR('a) p) v"
  by (simp add: heap_update_def heap_upd_list_def fun_eq_iff to_bytes_def)

lemma heap_list_heap_upd_list:
  "n \<le> addr_card \<Longrightarrow> length xs = n \<Longrightarrow> (\<And>xs. length xs = n \<Longrightarrow> length (f xs) = n) \<Longrightarrow>
    heap_list (heap_upd_list n p f h) n p = f (heap_list h n p)"
  unfolding heap_upd_list_def
  by (subst heap_list_heap_update_list_id) simp_all

lemma heap_upd_list_comp:
  assumes "n \<le> addr_card" "length xs = n"
  assumes f: "\<And>xs. length xs = n \<Longrightarrow> length (f xs) = n"
  assumes g: "\<And>xs. length xs = n \<Longrightarrow> length (g xs) = n"
  shows "heap_upd_list n p (f \<circ> g) = heap_upd_list n p f \<circ> heap_upd_list n p g"
  using assms
  by (simp add: fun_eq_iff heap_upd_list_def heap_list_heap_update_list_id
                heap_update_list_overwrite)

lemma heap_update_list_append:
  fixes v :: word8
  shows "heap_update_list s (xs @ ys) hp =
  heap_update_list (s + of_nat (length xs)) ys (heap_update_list s xs hp)"
proof (induct xs arbitrary: ys rule: rev_induct)
  case Nil
  show ?case by simp
next
  case (snoc v' vs')
  show ?case
    apply (simp add: snoc.hyps field_simps)
    apply (rule arg_cong [where f = "heap_update_list (1 + (s + of_nat (length vs'))) ys"])
    apply (rule ext)
    apply simp
    done
qed

lemma heap_update_list_super_update_bs:
  "length bs + n \<le> length bs' \<Longrightarrow> length bs' \<le> addr_card \<Longrightarrow>
    heap_update_list (p + of_nat n) bs (heap_update_list p bs' h) =
    heap_update_list p (super_update_bs bs bs' n) h"
  apply (subst super_update_bs_take_drop[symmetric, of n "length bs" bs'])
  unfolding super_update_bs_def heap_update_list_append
  apply simp_all
  apply (subst heap_update_list_commute)
  subgoal
    apply (subst (2) add_0_right[symmetric])
    unfolding intvl_disj_offset add.assoc
    apply (cases "length bs + n = length bs'")
    apply simp
    apply (intro intvl_disj_left)
    apply (simp_all add: addr_card_def card_word unat_of_nat_eq)
    done
  apply (subst heap_update_list_overwrite)
  apply simp_all
  done

lemma update_ti_adjust_ti:
  fixes t::"'a xtyp_info"
  and st::"'a xtyp_info_struct"
  and ts::"'a xtyp_info_tuple list"
  and x::"'a xtyp_info_tuple"
  assumes fg_cons: "fg_cons f g"
  shows
  "update_ti (adjust_ti t (f::'b \<Rightarrow> 'a) (g::'a \<Rightarrow> 'b \<Rightarrow> 'b)) bs v = g (update_ti t bs (f v)) v "
  "update_ti_struct (map_td_struct (\<lambda>n algn d. update_desc f g d) (update_desc f g) st) bs v = g (update_ti_struct st bs (f v)) v"
  "update_ti_list (map_td_list (\<lambda>n algn d. update_desc f g d) (update_desc f g) ts) bs v = g (update_ti_list ts bs (f v)) v"
  "update_ti_tuple (map_td_tuple (\<lambda>n algn d. update_desc f g d) (update_desc f g) x) bs v = g (update_ti_tuple x bs (f v)) v"
  unfolding adjust_ti_def
proof (induct t and st and ts and x arbitrary: v bs  and v bs and v bs and v bs)
  case (TypDesc nat typ_struct list)
  then show ?case by auto
next
  case (TypScalar nat1 nat2 a)
  then show ?case by (auto simp add: update_desc_def)
next
  case (TypAggregate list)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case using fg_cons by (auto simp add: fg_cons_def)
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case apply (cases dt_tuple) using fg_cons by (auto simp add: fg_cons_def)
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by auto
qed

lemma field_ti_field_lookupE:
  "\<lbrakk> field_ti TYPE('a :: c_type) f = Some t; \<And>n. \<lbrakk>field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n) \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
  unfolding field_ti_def
  by (clarsimp split: option.splits)

lemma field_ti_append_field_lookup:
  "field_ti TYPE('a::wf_type) f = Some u \<Longrightarrow> field_lookup u g l = Some (v, k) \<Longrightarrow>
    field_ti TYPE('a) (f @ g) = Some v"
  by (auto simp: field_ti_def field_lookup_append split: option.splits)

lemma field_tiD:
  "field_ti TYPE('a::mem_type) f = Some t \<Longrightarrow>
    field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, field_offset TYPE('a) f)"
  by (metis field_lookup_offset_eq field_ti_field_lookupE)

lemma wf_fd_field_lookup_mem_type: "field_lookup (typ_info_t(TYPE('a::mem_type))) f m = Some (s, n) \<Longrightarrow> wf_fd s"
  apply (erule wf_fd_field_lookupD)
  by simp

lemma wf_fd_field_ti_mem_type: "field_ti TYPE('a::mem_type) f = Some s \<Longrightarrow> wf_fd s"
  unfolding field_ti_def
  by (auto simp add: wf_fd_field_lookup_mem_type split: option.splits prod.splits)

lemma field_lookup_offset_non_zero:
  "NO_MATCH 0 m \<Longrightarrow> field_lookup t f 0 = Some (t', n) \<Longrightarrow> field_lookup t f m = Some (t', m + n)"
  by (simp add: field_lookup_offset' [where m'=0])

lemma field_lookup_append_Some:
  assumes wf: "wf_desc t"
  shows "field_lookup t (f@g) n = Some (s, m) \<Longrightarrow>
       \<exists>w k. field_lookup t f n = Some (w, k) \<and> field_lookup w g k = Some (s, m)"
  using wf
proof (induct n \<equiv> "length (f @ g)" arbitrary: f g n s m t)
  case 0
  then show ?case by auto
next
  case (Suc n)
  show ?case
    by (metis Suc.prems(1) Suc.prems(2)
        field_lookup_prefix_None''(1) field_lookup_prefix_Some''(1) not_Some_eq_tuple)
qed

section \<open>\<open>merge_ti\<close>\<close>

definition merge_ti :: "('a field_desc, 'b) typ_desc \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "merge_ti t a b = update_ti t (access_ti\<^sub>0 t a) b"

lemma merge_ti_adjust_ti[simp]:
  "fg_cons g s \<Longrightarrow> merge_ti (adjust_ti (typ_info_t TYPE('a::xmem_type)) g s) = (\<lambda>a. s (g a))"
  by (simp add: fun_eq_iff merge_ti_def update_ti_adjust_ti)

lemma is_scene_merge_ti:
  assumes t: "field_ti TYPE('a::xmem_type) f = Some t" shows "is_scene (merge_ti t)"
proof -
  interpret padding_lense "access_ti t" "update_ti t" "size_td t"
    using t[THEN field_tiD] by (rule field_lookup_padding_lense)

  show ?thesis
  proof
    show "merge_ti t (merge_ti t a b) c = merge_ti t a c" for a b c
      by (simp_all add: merge_ti_def access_ti\<^sub>0_def) (metis access_update update_access)
  qed (simp_all add: merge_ti_def access_ti\<^sub>0_def update_access double_update)
qed

lemma merge_ti_update_ti_disj:
  assumes *: "field_ti TYPE('a::xmem_type) f = Some t" "field_ti TYPE('a::xmem_type) g = Some u"
    and f_g: "disj_fn f g"
  assumes bs: "length bs = size_td u"
  shows "merge_ti t x (update_ti u bs y) = update_ti u bs (merge_ti t x y)"
proof -
  have eq[simp]: "\<And>ts us x. length ts = size_td t \<Longrightarrow> length us = size_td u \<Longrightarrow>
    update_ti t ts (update_ti u us x) = update_ti u us (update_ti t ts x)"
    using fu_commutes_lookup_disjD[OF *[THEN field_tiD] f_g]
    by (simp add: wf_lf_fdp fu_commutes_def update_ti_t_def split: if_splits)
  have [simp]: "wf_fd t" "wf_fd u"
    using *[THEN wf_fd_field_ti_mem_type] by auto
  show ?thesis
    by (simp add: merge_ti_def access_ti\<^sub>0_def length_fa_ti bs)
qed

lemma disjnt_scene_merge_ti:
  assumes *: "field_ti TYPE('a) f = Some t" "field_ti TYPE('a::xmem_type) g = Some u"
    and f_g: "disj_fn f g"
  shows "disjnt_scene (merge_ti t) (merge_ti u)"
  apply (clarsimp simp: disjnt_scene_def)
  apply (subst (2 3) merge_ti_def)
  apply (rule merge_ti_update_ti_disj[OF assms])
  apply (simp add: *[THEN wf_fd_field_ti_mem_type] length_fa_ti access_ti\<^sub>0_def)
  done

lemma access_ti_merge_ti_sub:
  assumes r: "field_ti TYPE('a::xmem_type) r = Some t" and t: "field_lookup t f 0 = Some (v, n)"
    and bs: "length bs = size_td v"
  shows "access_ti v (merge_ti t x y) bs = access_ti v x bs"
proof -
  let ?xbs = "super_update_bs bs (replicate (size_td t) 0) n"
  let ?x_y = "update_ti t (access_ti t x (replicate (size_td t) 0)) y"
  have wf_t: "wf_fd t" "wf_desc t" "wf_size_desc t"
    using wf_fd_field_ti_mem_type[OF r] r
      field_lookup_wf_desc_pres(1)[of "typ_info_t TYPE('a)" "r" 0]
      field_lookup_wf_size_desc_pres(1)[of "typ_info_t TYPE('a)" "r" 0]
    by (auto elim: field_ti_field_lookupE)

  have length_xbs: "length ?xbs = size_td t"
    using field_lookup_offset_size'[OF t] by (subst length_super_update_bs) (simp_all add: bs)
  have n_t: "n \<le> length (replicate (size_td t) 0)"
    using field_lookup_offset_size'[OF t] by auto
  have eq: "access_ti v x bs =
    take (size_td v) (drop n (access_ti t x (super_update_bs bs (replicate (size_td t) 0) n)))"
    for x
    using field_lookup_access_ti_take_drop[OF t wf_t length_xbs]
    unfolding take_drop_super_update_bs[OF bs n_t] .

  from wf_fd_consD[OF wf_t(1)]
  have eq_ac:
    "length bs = size_td t \<Longrightarrow> length bs' = size_td t \<Longrightarrow>
        access_ti t (update_ti t bs v) bs' = access_ti t (update_ti t bs v') bs'"
    "length bs = size_td t \<Longrightarrow> update_ti t (access_ti t v bs) v = v"
    for bs bs' v v'
    by (auto simp: fd_cons_def fd_cons_desc_def fd_cons_update_access_def
                   fd_cons_access_update_def update_ti_t_def length_fa_ti wf_t)

  have [simp]: "access_ti v ?x_y bs = access_ti v x bs" unfolding eq
    by (subst eq_ac(1)[of _ _ _ x]) (simp_all add: wf_t length_fa_ti length_xbs eq_ac)
  show ?thesis
    by (simp add: merge_ti_def fd_cons_access_update_def access_ti\<^sub>0_def)
qed

lemma access_ti_merge_ti_disj:
  assumes f: "field_ti TYPE('a::xmem_type) f = Some t"
  assumes g: "field_ti TYPE('a::xmem_type) g = Some u"
    and f_g: "disj_fn f g"
    and bs: "length bs = size_td u"
  shows "access_ti u (merge_ti t x y) bs = access_ti u y bs"
  apply (subst is_scene.idem[symmetric, OF is_scene_merge_ti, OF g, of y])
  apply (subst disjnt_sceneD[OF disjnt_scene_merge_ti, OF f g f_g])
  apply (rule access_ti_merge_ti_sub[OF g field_lookup_empty bs])
  done

lemma merge_ti_update_ti_sub:
  assumes r: "field_ti TYPE('a::xmem_type) r = Some t"
    and t: "field_lookup t f 0 = Some (v, n)"
    and bs: "length bs = size_td v"
  shows "merge_ti t x (update_ti v bs y) = merge_ti t x y"
proof -
  have wf_t: "wf_fd t" "wf_desc t" "wf_size_desc t"
    using wf_fd_field_ti_mem_type[OF r] r
      field_lookup_wf_desc_pres(1)[of "typ_info_t TYPE('a)" "r" 0]
      field_lookup_wf_size_desc_pres(1)[of "typ_info_t TYPE('a)" "r" 0]
    by (auto elim: field_ti_field_lookupE)

  from wf_fd_consD[OF wf_t(1)]
  have eq_uu:
    "length bs = size_td t \<Longrightarrow> length bs' = size_td t \<Longrightarrow>
      update_ti t bs (update_ti t bs' v) = update_ti t bs v"
    for bs bs' v
    by (auto simp: fd_cons_def fd_cons_desc_def fd_cons_double_update_def update_ti_t_def
                   length_fa_ti wf_t split: if_splits)

  from wf_fd_consD[OF wf_t(1)]
  have eq_ua:
    "length bs = size_td t \<Longrightarrow> update_ti t (access_ti t v bs) v = v"
    for bs v
    by (auto simp: fd_cons_def fd_cons_desc_def fd_cons_update_access_def update_ti_t_def
                   length_fa_ti wf_t split: if_splits)

  have n_v_t: "n + size_td v \<le> size_td t"
    using field_lookup_offset_size'[OF t] by simp
  with fi_fu_consistentD[OF t wf_t(1)] have eq_u_sub:
    "length bs' = size_td v \<Longrightarrow> length bs = size_td t \<Longrightarrow>
      update_ti t (super_update_bs bs' bs n) y =
      update_ti v bs' (update_ti t bs y)" for bs' y bs
    by (simp add: update_ti_t_def)

  have "update_ti v bs y =
    update_ti v bs (update_ti t (access_ti t y (replicate (size_td t) 0)) y)"
    by (subst eq_ua) (simp_all add: bs)
  also have "\<dots> = update_ti t (super_update_bs bs (access_ti t y (replicate (size_td t) 0)) n) y"
    by (subst eq_u_sub) (simp_all add: bs length_fa_ti wf_t)
  finally show ?thesis
    using bs n_v_t by (simp add: access_ti\<^sub>0_def length_fa_ti wf_t eq_uu merge_ti_def)
qed

lemma merge_ti_merge_ti_sub1:
  assumes t: "field_ti TYPE('a::xmem_type) f = Some t"
  assumes u: "field_ti TYPE('a) (f @ g) = Some u"
  shows "merge_ti t a (merge_ti u a b) = merge_ti t a b"
proof -
  obtain n m where n: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n)"
    and m: "field_lookup (typ_info_t TYPE('a)) (f@g) 0 = Some (u, m)"
    using t u by (auto elim!: field_ti_field_lookupE)
  from n field_lookup_append_Some[OF _ m] have u': "field_lookup t g 0 = Some (u, m - n)"
    by (simp add: CTypes.field_lookup_offset2)
  have [simp]: "fd_cons u"
    using fd_cons fd_consistentD m by blast
  show ?thesis
    by (subst (2) merge_ti_def)
       (simp add: merge_ti_update_ti_sub[OF t u'] fd_cons_length_p)
qed

lemma merge_ti_merge_ti_sub2:
  assumes t: "field_ti TYPE('a::xmem_type) f = Some t"
  assumes u: "field_ti TYPE('a) (f @ g) = Some u"
  shows "merge_ti u a (merge_ti t a b) = merge_ti t a b"
proof -
  obtain n m where n: "field_lookup (typ_info_t TYPE('a)) f 0 = Some (t, n)"
    and m: "field_lookup (typ_info_t TYPE('a)) (f@g) 0 = Some (u, m)"
    using t u by (auto elim!: field_ti_field_lookupE)
  from n field_lookup_append_Some[OF _ m] have u': "field_lookup t g 0 = Some (u, m - n)"
    by (simp add: CTypes.field_lookup_offset2)
  have [simp]: "fd_cons u"
    using fd_cons fd_consistentD m by blast

  interpret u: is_scene "merge_ti u"
    using u by (rule is_scene_merge_ti)

  have eq: "access_ti\<^sub>0 u a = access_ti\<^sub>0 u (merge_ti t a b)"
    by (simp add: access_ti_merge_ti_sub[OF t u'] access_ti\<^sub>0_def)
  show ?thesis
    apply (subst (1) merge_ti_def)
    apply (subst eq)
    apply (subst (1) merge_ti_def[symmetric])
    apply (rule u.idem)
    done
qed

lemma comm_scene_merge_ti_sub:
  assumes *: "field_ti TYPE('a::xmem_type) f = Some t" "field_ti TYPE('a) (f @ g) = Some u"
  shows "comm_scene (merge_ti t) (merge_ti u)"
  by (clarsimp simp: comm_scene_def merge_ti_merge_ti_sub1[OF *] merge_ti_merge_ti_sub2[OF *])

lemma comm_scene_merge_ti:
  assumes *: "field_ti TYPE('a::xmem_type) f = Some t" "field_ti TYPE('a) g = Some u"
  shows "comm_scene (merge_ti t) (merge_ti u)"
proof cases
  assume "disj_fn f g"
  from disjnt_scene_merge_ti[OF * this] show ?thesis
    by blast
next
  assume "\<not> disj_fn f g"
  with * show ?thesis
    by (auto simp: disj_fn_def less_eq_list_def prefix_def intro: comm_scene_merge_ti_sub)
qed

subsection \<open>\<open>merge_ti_list\<close>\<close>

definition merge_ti_list where
  "merge_ti_list ts a = fold (\<lambda>t. merge_ti t a) ts"

lemma is_scene_merge_ti_list:
  "list_all (\<lambda>u. \<exists>f. field_ti TYPE('a::xmem_type) f = Some u) ts \<Longrightarrow>
    is_scene (merge_ti_list ts)"
  unfolding merge_ti_list_def
  apply (intro is_scene_fold')
  by (auto simp: list_all_iff pairwise_def is_scene_merge_ti)
   (meson comm_scene_merge_ti)

lemma merge_ti_list_nil[simp]: "merge_ti_list [] = (\<lambda>a. id)"
  by (simp add: merge_ti_list_def fun_eq_iff)

lemma merge_ti_list_cons[simp]:
  "merge_ti_list (t # ts) a = merge_ti_list ts a \<circ> merge_ti t a"
  by (simp add: merge_ti_list_def)

lemma merge_ti_list_append[simp]:
  "merge_ti_list (ts @ ts') x y = merge_ti_list ts' x (merge_ti_list ts x y)"
  by (simp add: merge_ti_list_def)

lemma access_ti_merge_ti_list:
  assumes ts: "list_all (\<lambda>(f, u). field_ti TYPE('a::xmem_type) f = Some u) ts"
      "distinct_prop disj_fn (map fst ts)"
    and r_t: "(r, t) \<in> set ts" and v: "field_lookup t f 0 = Some (v, n)"
    and bs: "length bs = size_td v"
  shows "access_ti v (merge_ti_list (map snd ts) x y) bs = access_ti v x bs"
  using ts r_t
proof (induction ts rule: rev_induct)
  case (snoc r_t ts)
  from this(2,3) have *:
    "list_all (\<lambda>(f, u). field_ti TYPE('a) f = Some u) ts"
    "distinct_prop disj_fn (map fst ts)"
    and disj: "\<forall>t\<in>set ts. disj_fn (fst t) (fst r_t)"
    and **: "field_ti TYPE('a) (fst r_t) = Some (snd r_t)"
    by (auto simp: distinct_prop_append)

  show ?case
  proof cases
    assume [simp]: "r_t = (r, t)"
    with ** have ft_r: "field_ti TYPE('a) r = Some t" by simp
    show ?thesis
      by (simp add: access_ti_merge_ti_sub[OF ft_r v bs])
  next
    assume "r_t \<noteq> (r, t)"
    with snoc.prems have r_t: "(r, t) \<in> set ts" by auto
    with * have "field_ti TYPE('a) r = Some t"
      by (auto simp: list_all_iff)
    from field_ti_append_field_lookup[OF this v]
    have r_f: "field_ti TYPE('a) (r @ f) = Some v" .
    from r_t disj
    have "disj_fn (fst r_t) r" by (auto simp: disj_fn_def)
    then have disj: "disj_fn (fst r_t) (r @ f)"
      by (rule disj_fn_append_right)
    from snoc.IH[OF * r_t] show ?thesis
      by (simp add: access_ti_merge_ti_disj[OF ** r_f disj bs])
  qed
qed simp

lemma merge_ti_list_update_ti:
  assumes ts: "list_all (\<lambda>(f, u). field_ti TYPE('a::xmem_type) f = Some u) ts" "(f_t, t) \<in> set ts"
    and disj: "distinct_prop disj_fn (map fst ts)"
    and t: "field_lookup t f 0 = Some (v, n)"
    and bs: "length bs = size_td v"
  shows "merge_ti_list (map snd ts) x (update_ti v bs y) = merge_ti_list (map snd ts) x y"
  using ts disj
proof (induction ts arbitrary: y)
  case (Cons u' ts)
  then obtain t' f' where ts[simp]: "list_all (\<lambda>(f, u). field_ti TYPE('a) f = Some u) ts"
    and f': "field_ti TYPE('a) f' = Some t'"
    and t': "t = t' \<or> (t \<noteq> t' \<and> (f_t, t) \<in> set ts)" and u': "u' = (f', t')"
    and f'_ts: "\<forall>x\<in>set ts. disj_fn f' (fst x)"
    and [simp]: "distinct_prop disj_fn (map fst ts)"
    by auto

  from Cons have f_t: "field_ti TYPE('a) f_t = Some t"
    by (auto simp: list_all_iff)

  show ?case using t'
  proof (elim disjE conjE)
    assume t_eq: "t = t'"
    have "merge_ti t' x (update_ti v bs y) = merge_ti t' x y"
      using f' t[unfolded t_eq] bs by (rule merge_ti_update_ti_sub)
    then show ?thesis
      by (simp add: u')
  next
    assume ne: "t \<noteq> t'" and mem: "(f_t, t) \<in> set ts"
    with f'_ts have "disj_fn f' f_t" by auto
    then have disj: "disj_fn f' (f_t @ f)"
      by (rule disj_fn_append_right)
    have "merge_ti t' x (update_ti v bs y) = update_ti v bs (merge_ti t' x y)"
      using f' field_ti_append_field_lookup[OF f_t t] disj bs by (rule merge_ti_update_ti_disj)
    then show ?thesis
      by (simp add: Cons mem u')
  qed
qed simp

lemma heap_update_eq_fold_subfields:
  assumes ts: "list_all (\<lambda>(f, u). field_ti TYPE('a::xmem_type) f = Some u) ts"
  shows "heap_update p x =
    fold (\<lambda>(f, u). heap_upd_list (size_td u) &(p\<rightarrow>f) (access_ti u x)) ts \<circ>
    heap_upd_list (size_of TYPE('a)) (ptr_val p)
      (access_ti (typ_info_t TYPE('a)) (merge_ti_list (map snd ts) y x))"
proof -
  have snd_ts: "list_all (\<lambda>u. \<exists>f. field_ti TYPE('a::xmem_type) f = Some u) (map snd ts)"
    using ts unfolding list.pred_map by (rule list.pred_mono_strong) auto
  then interpret merge_ti_list: is_scene "merge_ti_list (map snd ts)"
    by (rule is_scene_merge_ti_list)

  have "heap_upd_list (size_of TYPE('a)) (ptr_val p)
      (access_ti (typ_info_t TYPE('a)) (merge_ti_list (map snd ts) x z)) =
    fold (\<lambda>(f, u). heap_upd_list (size_td u) &(p\<rightarrow>f) (access_ti u x)) ts \<circ>
      heap_upd_list (size_of TYPE('a)) (ptr_val p) (access_ti (typ_info_t TYPE('a)) z)" for z
    using ts
  proof (induction ts arbitrary: z)
    case (Cons t ts)
    then obtain f u where ts: "list_all (\<lambda>a. case a of (f, u) \<Rightarrow> field_ti TYPE('a) f = Some u) ts"
      and f: "field_ti TYPE('a) f = Some u" and t: "t = (f, u)"
      by (cases t) auto

    have wf_u: "wf_fd u" using f by (rule wf_fd_field_ti_mem_type)
    have sz[arith]: "size_td u + field_offset TYPE('a) f \<le> size_of TYPE('a)"
      using f[THEN field_tiD, THEN field_lookup_offset_size'] by (simp add: size_of_def)

    interpret padding_lense "access_ti u" "update_ti u" "size_td u"
      by (rule field_lookup_padding_lense[OF field_tiD, OF f])
    from field_access_eq_padding1[unfolded eq_padding_def]
    have access_ti_access_ti:
      "length bs = size_td u \<Longrightarrow> access_ti u v (access_ti u w bs) = access_ti u v bs" for v w bs
      by auto

    have "heap_upd_list (size_of TYPE('a)) (ptr_val p)
        (access_ti (typ_info_t TYPE('a)) (update_ti u (access_ti\<^sub>0 u x) z)) =
      heap_upd_list (size_td u) &(p\<rightarrow>f) (access_ti u x) \<circ>
      heap_upd_list (size_of TYPE('a)) (ptr_val p) (access_ti (typ_info_t TYPE('a)) z)"
      apply (rule ext)
      subgoal for h unfolding heap_upd_list_def
        apply (simp add:  field_lvalue_def)
        apply (subst heap_list_update_list)
        subgoal by (simp add: lense.access_result_size)
        subgoal by (simp add: lense.access_result_size)
        apply (subst heap_update_list_super_update_bs)
        subgoal by (simp add: lense.access_result_size length_fa_ti wf_u)
        subgoal using max_size[where 'a='a, arith] by (simp add: lense.access_result_size)
        apply (subst mem_type_field_lookup_access_ti_take_drop[symmetric])
        apply (rule f[THEN field_tiD])
        apply simp
        apply (subst access_ti_access_ti)
        apply simp
        apply (subst mem_type_access_ti_super_update_bs[symmetric, OF field_tiD, OF f])
        apply (simp_all add: super_update_bs_take_drop)
        done
      done
    then show ?case
      unfolding fold_Cons t by (simp add: Cons.IH[OF ts] merge_ti_def)
  qed simp
  then show ?thesis
    apply (subst heap_update_eq_heap_upd_list)
    apply (subst merge_ti_list.idem[symmetric])
    apply (subst merge_ti_list.right[symmetric])
    apply (simp del: merge_ti_list.right)
    done
qed

end