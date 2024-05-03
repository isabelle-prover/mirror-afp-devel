(*
 * Copyright 2020, Data61, CSIRO (ABN 41 687 119 230)
 * Copyright (c) 2022 Apple Inc. All rights reserved.
 *
 * SPDX-License-Identifier: BSD-2-Clause
 *)

theory CTypes
imports
  CTypesDefs "HOL-Eisbach.Eisbach_Tools"
begin

section \<open>\<open>super_update_bs\<close>\<close>

lemma length_super_update_bs [simp]:
  "n + length v \<le> length bs \<Longrightarrow> length (super_update_bs v bs n) = length bs"
  by (clarsimp simp: super_update_bs_def)

lemma drop_super_update_bs:
  "\<lbrakk> k \<le> n; n \<le> length bs \<rbrakk> \<Longrightarrow> drop k (super_update_bs v bs n) = super_update_bs v (drop k bs) (n - k)"
  by (simp add: super_update_bs_def take_drop)

lemma drop_super_update_bs2:
  "\<lbrakk> n \<le> length bs; n + length v \<le> k \<rbrakk> \<Longrightarrow>
      drop k (super_update_bs v bs n) = drop k bs"
  by (clarsimp simp: super_update_bs_def min_def split: if_split_asm)

lemma take_super_update_bs:
  "\<lbrakk> k \<le> n; n \<le> length bs \<rbrakk> \<Longrightarrow> take k (super_update_bs v bs n) = take k bs"
  by (clarsimp simp: super_update_bs_def min_def split: if_split_asm)

lemma take_super_update_bs2:
  "\<lbrakk> n \<le> length bs; n + length v \<le> k \<rbrakk> \<Longrightarrow>
      take k (super_update_bs v bs n) = super_update_bs v (take k bs) n"
  apply (clarsimp simp: super_update_bs_def min_def split: if_split_asm)
  apply (cases "n=k"; simp add: drop_take)
  done

lemma take_drop_super_update_bs:
  "length v = n \<Longrightarrow> m \<le> length bs \<Longrightarrow> take n (drop m (super_update_bs v bs m)) = v"
  by (simp add: super_update_bs_def)

lemma super_update_bs_take_drop:
  "n + m \<le> length bs \<Longrightarrow> super_update_bs (take m (drop n bs)) bs n = bs"
  by (simp add: super_update_bs_def) (metis append.assoc append_take_drop_id take_add)

lemma super_update_bs_same_length: "length bs = length xbs \<Longrightarrow> super_update_bs bs xbs 0 = bs"
  by (simp add: super_update_bs_def)

lemma super_update_bs_append_drop_first:
  "length xbs = m \<Longrightarrow> n + length bs \<le> m \<Longrightarrow> drop m (super_update_bs bs (xbs @ ybs) n) = ybs"
  by (simp add: super_update_bs_def)

lemma super_update_bs_append_take_first:
  "length xbs = m \<Longrightarrow> n + length bs \<le> m \<Longrightarrow> take m (super_update_bs bs (xbs @ ybs) n) = (super_update_bs bs xbs n)"
  by (simp add: super_update_bs_def)

lemma super_update_bs_append_drop_second:
  "length xbs = m \<Longrightarrow> m \<le> n  \<Longrightarrow>
  drop m (super_update_bs bs (xbs @ ybs) n) = (super_update_bs bs ybs (n - m))"
  by (simp add: super_update_bs_def)

lemma super_update_bs_append_take_second:
  "length xbs = m \<Longrightarrow> m \<le> n  \<Longrightarrow>
  take m (super_update_bs bs (xbs @ ybs) n) = xbs"
  by (simp add: super_update_bs_def)

lemma super_update_bs_length: "length bs + n \<le> length xbs ==> length (super_update_bs bs xbs n) = length xbs"
  by (simp add: super_update_bs_def)

lemma super_update_bs_append2: "length xbs \<le> n   \<Longrightarrow>
  super_update_bs bs (xbs @ ybs) n =  xbs @ super_update_bs bs ybs (n - length xbs)"
  by (simp add: super_update_bs_def)

lemma super_update_bs_append1: "n + length bs \<le> length xbs \<Longrightarrow>
  super_update_bs bs (xbs @ ybs) n = super_update_bs bs xbs n @ ybs"
  by (simp add: super_update_bs_def)

section \<open>Rest\<close>


lemma fu_commutes:
  "fu_commutes f g \<Longrightarrow> f bs (g bs' v) = g bs' (f bs v)"
  by (simp add: fu_commutes_def)


lemma size_td_list_append [simp]:
  "size_td_list (xs@ys) = size_td_list xs + size_td_list ys"
  by (induct xs) (auto)


lemma access_ti_append:
  "\<And>bs. length bs = size_td_list (xs@ys) \<Longrightarrow>
      access_ti_list (xs@ys) t bs =
          access_ti_list xs t (take (size_td_list xs) bs) @
          access_ti_list ys t (drop (size_td_list xs) bs)"
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons x xs) thus ?case by (simp add: min_def ac_simps drop_take)
qed

lemma update_ti_append [simp]:
  "\<And>bs. update_ti_list (xs@ys) bs v =
      update_ti_list xs (take (size_td_list xs) bs)
          (update_ti_list ys (drop (size_td_list xs) bs) v)"
proof (induct xs)
  case Nil show ?case by simp
next
  case (Cons x xs) thus ?case by (simp add: drop_take ac_simps min_def)
qed

lemma update_ti_struct_t_typscalar [simp]:
  "update_ti_struct_t (TypScalar n algn d) =
      (\<lambda>bs. if length bs = n then field_update d bs else id)"
  by (rule ext, simp add: update_ti_struct_t_def)

lemma update_ti_list_t_empty [simp]:
  "update_ti_list_t [] = (\<lambda>x. id)"
  by (rule ext, simp add: update_ti_list_t_def)

lemma update_ti_list_t_cons [simp]:
  "update_ti_list_t (x#xs) = (\<lambda>bs v.
      if length bs = size_td_tuple x + size_td_list xs then
          update_ti_tuple_t x (take (size_td_tuple x) bs)
              (update_ti_list_t xs (drop (size_td_tuple x) bs) v) else
          v)"
  by (force simp: update_ti_list_t_def update_ti_tuple_t_def min_def)

lemma update_ti_append_s [simp]:
  "\<And>bs. update_ti_list_t (xs@ys) bs v = (
      if length bs = size_td_list xs + size_td_list ys then
          update_ti_list_t xs (take (size_td_list xs) bs)
              (update_ti_list_t ys (drop (size_td_list xs) bs) v) else
          v)"
proof (induct xs)
  case Nil show ?case by (simp add: update_ti_list_t_def)
next
  case (Cons x xs) thus ?case by (simp add: min_def drop_take ac_simps)
qed

lemma update_ti_tuple_t_dtuple [simp]:
  "update_ti_tuple_t (DTuple t f d) = update_ti_t t"
  by (rule ext, simp add: update_ti_tuple_t_def update_ti_t_def)

text \<open>---------------------------------------------------------------\<close>

lemma field_desc_empty [simp]:
  "field_desc (TypDesc algn (TypAggregate []) nm) =
    \<lparr> field_access = \<lambda>x bs. [],
      field_update = \<lambda>x. id, field_sz = 0 \<rparr>"
  by (force simp: update_ti_t_def)


lemma export_uinfo_typdesc_simp [simp]:
  "export_uinfo (TypDesc algn st nm) = map_td field_norm (\<lambda>_. ()) (TypDesc algn st nm)"
  by (simp add: export_uinfo_def)

lemma map_td_list_append [simp]:
  "map_td_list f g (xs@ys) = map_td_list f g xs @ map_td_list f g ys"
  by (induct xs) auto

lemma map_td_id:
  "map_td (\<lambda>n algn. id) id t = (t::('a, 'b) typ_desc)"
  "map_td_struct (\<lambda>n algn. id) id st = (st::('a, 'b) typ_struct)"
  "map_td_list (\<lambda>n algn. id) id ts = (ts::('a, 'b) typ_tuple list)"
  "map_td_tuple (\<lambda>n algn. id) id x = (x::('a, 'b) typ_tuple)"
  by (induction t and st and ts and x) simp_all


lemma dt_snd_map_td_list:
  "dt_snd ` set (map_td_list f g ts) = dt_snd ` set ts"
proof (induct ts)
  case (Cons x xs) thus ?case by (cases x) auto
qed simp

lemma wf_desc_map:
  shows "wf_desc (map_td f g t) = wf_desc t" and
        "wf_desc_struct (map_td_struct f g st) = wf_desc_struct st" and
        "wf_desc_list (map_td_list f g ts) = wf_desc_list ts" and
        "wf_desc_tuple (map_td_tuple f g x) = wf_desc_tuple x"
proof (induct t and st and ts and x)
  case (Cons_typ_desc x xs) thus ?case
    by (cases x, auto simp: dt_snd_map_td_list)
qed auto

lemma wf_desc_list_append [simp]:
  "wf_desc_list (xs@ys) =
   (wf_desc_list xs \<and> wf_desc_list ys \<and> dt_snd ` set xs \<inter> dt_snd ` set ys = {})"
  by (induct xs) auto

lemma wf_size_desc_list_append [simp]:
  "wf_size_desc_list (xs@ys) = (wf_size_desc_list xs \<and> wf_size_desc_list ys)"
  by (induct xs) auto

lemma norm_tu_list_append [simp]:
  "norm_tu_list (xs@ys) bs =
   norm_tu_list xs (take (size_td_list xs) bs) @ norm_tu_list ys (drop (size_td_list xs) bs)"
  by (induct xs arbitrary: bs, auto simp: min_def ac_simps drop_take)

lemma wf_size_desc_gt:
  shows "wf_size_desc (t::('a, 'b) typ_desc) \<Longrightarrow> 0 < size_td t" and
        "wf_size_desc_struct st \<Longrightarrow> 0 < size_td_struct (st::('a,'b) typ_struct)" and
        "\<lbrakk> ts \<noteq> []; wf_size_desc_list ts \<rbrakk> \<Longrightarrow> 0 < size_td_list (ts::('a,'b) typ_tuple list)" and
        "wf_size_desc_tuple x \<Longrightarrow> 0 < size_td_tuple (x::('a,'b) typ_tuple)"
  by (induct t and st and ts and x rule: typ_desc_typ_struct_inducts, auto)

lemma field_lookup_empty [simp]:
  "field_lookup t [] n = Some (t,n)"
  by (cases t) clarsimp

lemma field_lookup_tuple_empty [simp]:
  "field_lookup_tuple x [] n = None"
  by (cases x) clarsimp

lemma field_lookup_list_empty [simp]:
  "field_lookup_list ts [] n = None"
  by (induct ts arbitrary: n) auto

lemma field_lookup_struct_empty [simp]:
  "field_lookup_struct st [] n = None"
  by (cases st) auto

lemma field_lookup_list_append:
  "field_lookup_list (xs@ys) f n = (case field_lookup_list xs f n of
                                      None \<Rightarrow> field_lookup_list ys f (n + size_td_list xs)
                                    | Some y \<Rightarrow> Some y)"
proof (induct xs arbitrary: n)
  case Nil show ?case by simp
next
  case (Cons x xs) thus ?case
    by (cases x) (auto simp: ac_simps split: option.splits)
qed

lemma field_lookup_list_None:
  "f \<notin> dt_snd ` set ts \<Longrightarrow> field_lookup_list ts (f#fs) m = None"
proof (induct ts arbitrary: f fs m)
  case (Cons x _) thus ?case by (cases x) auto
qed simp

lemma field_lookup_list_Some:
  "f \<in> dt_snd ` set ts \<Longrightarrow> field_lookup_list ts [f] m \<noteq> None"
proof (induct ts arbitrary: f m)
  case (Cons x _) thus ?case by (cases x) auto
qed simp

lemma field_lookup_offset_le:
  shows "\<And>s m n f. field_lookup t f m = Some ((s::('a,'b) typ_desc),n) \<Longrightarrow> m \<le> n" and
        "\<And>s m n f. field_lookup_struct st f m = Some ((s::('a,'b) typ_desc),n) \<Longrightarrow> m \<le> n" and
        "\<And>s m n f. field_lookup_list ts f m = Some ((s::('a, 'b) typ_desc),n) \<Longrightarrow> m \<le> n" and
        "\<And>s m n f. field_lookup_tuple x f m = Some ((s::('a, 'b) typ_desc),n) \<Longrightarrow> m \<le> n"
proof (induct t and st and ts and x)
  case (Cons_typ_desc x xs) thus ?case by (fastforce split: option.splits)
qed (auto split: if_split_asm)

lemma field_lookup_offset':
  shows "\<And>f m m' n t'. (field_lookup t f m = Some ((t'::('a,'b) typ_desc),m + n)) =
          (field_lookup t f m' = Some (t',m' + n))" and
        "\<And>f m m' n t'. (field_lookup_struct st f m = Some ((t'::('a,'b) typ_desc),m + n)) =
          (field_lookup_struct st f m' = Some (t',m' + n))" and
        "\<And>f m m' n t'. (field_lookup_list ts f m = Some ((t'::('a,'b) typ_desc),m + n)) =
          (field_lookup_list ts f m' = Some (t',m' + n))" and
        "\<And>f m m' n t'. (field_lookup_tuple x f m = Some ((t'::('a,'b) typ_desc),m + n)) =
          (field_lookup_tuple x f m' = Some (t',m' + n))"
proof (induct t and st and ts and x)
  case (Cons_typ_desc x xs)
  show ?case
  proof
    assume ls: "field_lookup_list (x # xs) f m = Some (t', m + n)"
    show "field_lookup_list (x # xs) f m' = Some (t', m' + n)" (is "?X")
    proof cases
      assume ps: "field_lookup_tuple x f m = None"
      moreover from this ls have "\<exists>k. n = size_td (dt_fst x) + k"
        by (clarsimp dest!: field_lookup_offset_le, arith)
      moreover have "field_lookup_tuple x f m' = None"
        apply (rule ccontr)
        using ps
        apply clarsimp
        subgoal premises prems for a b
        proof -
          obtain k where "b = m' + k"
            using prems field_lookup_offset_le
            by (metis less_eqE)
        then show ?thesis
          using prems
          by (clarsimp simp: Cons_typ_desc [where m'=m])
      qed
      done
      ultimately show "?X" using ls
        by (clarsimp simp: add.assoc [symmetric])
           (subst (asm) Cons_typ_desc [where m'="m' + size_td (dt_fst x)"], fast)
    next
      assume nps: "field_lookup_tuple x f m \<noteq> None"
      moreover from this have "field_lookup_tuple x f m' \<noteq> None"
        apply (clarsimp)
        subgoal premises prems for a b
        proof -
          obtain k where "b = m + k"
            using prems field_lookup_offset_le
            by (metis less_eqE)
          then show ?thesis 
            using prems
            apply clarsimp
            apply (subst (asm) Cons_typ_desc [where m'=m']) 
            apply fast
            done
        qed
        done
      ultimately show "?X" using ls
        by (clarsimp, subst (asm) Cons_typ_desc [where m'=m'], simp)
    qed
  next
    assume ls: "field_lookup_list (x # xs) f m' = Some (t', m' + n)"
    show "field_lookup_list (x # xs) f m = Some (t', m + n)" (is "?X")
    proof cases
      assume ps: "field_lookup_tuple x f m' = None"
      moreover from this ls have "\<exists>k. n = size_td (dt_fst x) + k"
        by (clarsimp dest!: field_lookup_offset_le, arith)
      moreover have "field_lookup_tuple x f m = None"
        apply (rule ccontr)
        using ps
        apply clarsimp
        subgoal premises prems for a b
        proof -
          obtain k where "b = m + k"
            using prems field_lookup_offset_le
            by (metis less_eqE)
          then show ?thesis using prems
            by (clarsimp simp: Cons_typ_desc [where m'=m'])
        qed
        done
      ultimately show "?X" using ls
        by (clarsimp simp: add.assoc [symmetric])
           (subst (asm) Cons_typ_desc [where m'="m + size_td (dt_fst x)"], fast)
    next
      assume nps: "field_lookup_tuple x f m' \<noteq> None"
      moreover from this have "field_lookup_tuple x f m \<noteq> None"
        apply clarsimp
        subgoal premises prems for a b
        proof -
          obtain k where "b = m' + k"
            using prems field_lookup_offset_le
            by (metis less_eqE)
          then show ?thesis using prems
            apply clarsimp
            apply (subst (asm) Cons_typ_desc [where m'=m]) 
            apply fast
            done
        qed
        done
      ultimately show "?X" using ls
        by (clarsimp, subst (asm) Cons_typ_desc [where m'=m], simp)
    qed
  qed
qed auto

lemma field_lookup_offset:
  "(field_lookup t f m = Some (t',m + n)) = (field_lookup t f 0 = Some (t',n))"
  by (simp add: field_lookup_offset' [where m'=0])

lemma field_lookup_offset2:
  "field_lookup t f m = Some (t',n) \<Longrightarrow> field_lookup t f 0 = Some (t',n - m)"
  by (simp add: field_lookup_offset_le
           flip: field_lookup_offset [where m=m])

lemma field_lookup_list_offset:
  "(field_lookup_list ts f m = Some (t',m + n)) = (field_lookup_list ts f 0 = Some (t',n))"
  by (simp add: field_lookup_offset' [where m'=0])

lemma field_lookup_list_offset2:
  "field_lookup_list ts f m = Some (t',n) \<Longrightarrow> field_lookup_list ts f 0 = Some (t',n - m)"
  by (simp add: field_lookup_offset_le
           flip: field_lookup_list_offset [where m=m])

lemma field_lookup_list_offset3:
  "field_lookup_list ts f 0 = Some (t',n) \<Longrightarrow> field_lookup_list ts f m = Some (t',m + n)"
  by (simp add: field_lookup_list_offset)

lemma field_lookup_list_offsetD:
  "\<lbrakk> field_lookup_list ts f 0 = Some (s,k);
      field_lookup_list ts f m = Some (t,n) \<rbrakk> \<Longrightarrow> s=t \<and> n=m+k"
  subgoal premises prems
  proof - 
    have "\<exists>k. n = m + k" using prems field_lookup_offset_le by (metis less_eqE)
    then show ?thesis using prems
      by (clarsimp simp: field_lookup_list_offset)
  qed
  done

lemma field_lookup_offset_None:
  "(field_lookup t f m = None) = (field_lookup t f 0 = None)"
  by (auto simp: field_lookup_offset2 field_lookup_offset [where m=m,symmetric]
           intro: ccontr)

lemma field_lookup_list_offset_None:
  "(field_lookup_list ts f m = None) = (field_lookup_list ts f 0 = None)"
  by (auto simp: field_lookup_list_offset2 field_lookup_list_offset [where m=m,symmetric]
           intro: ccontr)

lemma map_td_size [simp]:
  shows "size_td (map_td f g t) = size_td t" and
        "size_td_struct (map_td_struct f g st) = size_td_struct st" and
        "size_td_list (map_td_list f g ts) = size_td_list ts" and
        "size_td_tuple (map_td_tuple f g x) = size_td_tuple x"
  by (induct t and st and ts and x, auto)

lemma td_set_map_td1:
"(s, n) \<in> td_set t k \<Longrightarrow> (map_td f g s, n) \<in> td_set (map_td f g t) k" and
"(s, n) \<in> td_set_struct st k \<Longrightarrow> (map_td f g s, n) \<in> td_set_struct (map_td_struct f g st) k" and
"(s, n) \<in> td_set_list ts k \<Longrightarrow> (map_td f g s, n) \<in> td_set_list (map_td_list f g ts) k" and
"(s, n) \<in> td_set_tuple td k \<Longrightarrow> (map_td f g s, n) \<in> td_set_tuple (map_td_tuple f g td) k"
     apply (induct t and st and ts and td arbitrary: n k and n k and n k and n k)
  by (auto, metis dt_tuple.collapse map_td_size(4) tz5)


lemma size_td_tuple_dt_fst:
  "size_td_tuple p = size_td (dt_fst p)"
  by (cases p, simp)

lemma td_set_map_td2:
"(s', n) \<in> td_set (map_td f g t) k \<Longrightarrow> \<exists>s. (s, n) \<in> td_set t k \<and> s' = map_td f g s" and
"(s', n) \<in> td_set_struct (map_td_struct f g st) k \<Longrightarrow> \<exists>s. (s, n) \<in> td_set_struct st k \<and> s' = map_td f g s" and
"(s', n) \<in> td_set_list (map_td_list f g ts) k \<Longrightarrow> \<exists>s. (s, n) \<in> td_set_list ts k \<and> s' = map_td f g s" and
"(s', n) \<in> td_set_tuple (map_td_tuple f g td) k \<Longrightarrow> \<exists>s. (s, n) \<in> td_set_tuple td k \<and> s' = map_td f g s"
proof (induct t and st and ts and td arbitrary: n k  and n k  and n k  and n k )
  case (TypDesc nat typ_struct list)
  then show ?case by auto
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
  then show ?case
      apply (clarsimp, safe)
     apply blast
    by (metis map_td_size(4) size_td_tuple_dt_fst)
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by auto
qed

lemma td_set_offset1:
"(s, n) \<in> td_set t k \<Longrightarrow> (s, n + l) \<in> td_set t (k + l)" and
"(s, n) \<in> td_set_struct st k \<Longrightarrow> (s, n + l) \<in> td_set_struct st (k + l)" and
"(s, n) \<in> td_set_list xs k \<Longrightarrow> (s, n + l) \<in> td_set_list xs (k + l)" and
"(s, n) \<in> td_set_tuple td k \<Longrightarrow> (s, n + l) \<in> td_set_tuple td (k + l)"
 apply (induct t and st and xs and td arbitrary: s n k l and  s n k l  and s n k l  and s n k l)
 by (auto, smt (verit, best) add.commute add.left_commute)

lemma td_set_offset2:
"(s, n + l) \<in> td_set t (k + l) \<Longrightarrow> (s, n) \<in> td_set t k" and
"(s, n + l) \<in> td_set_struct st (k + l) \<Longrightarrow> (s, n) \<in> td_set_struct st k" and
"(s, n + l) \<in> td_set_list xs (k + l) \<Longrightarrow> (s, n) \<in> td_set_list xs k" and
"(s, n + l) \<in> td_set_tuple td (k + l) \<Longrightarrow> (s, n) \<in> td_set_tuple td k"
 apply (induct t and st and xs and td arbitrary: s n k l and  s n k l  and s n k l  and s n k l)
 by (auto, smt (verit, best) add.commute add.left_commute)

lemma td_set_offset_conv: "(s, n) \<in> td_set t k  \<longleftrightarrow> (s, n + l) \<in> td_set t (k + l)"
  using td_set_offset1 td_set_offset2 by blast

lemma td_set_offset_0_conv: "(s, n + k) \<in> td_set t k \<longleftrightarrow> (s, n) \<in> td_set t 0 "
  using td_set_offset_conv [where k=0 and n=n and l=k and s=s and t =t]
  by simp

lemma td_set_offset_le':
  "\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set t m \<longrightarrow> m \<le> n"
  "\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set_struct st m \<longrightarrow> m \<le> n"
  "\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set_list ts m \<longrightarrow> m \<le> n"
  "\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set_tuple x m \<longrightarrow> m \<le> n"
  by (induct t and st and ts and x) fastforce+

lemma td_set_offset_0_conv': "(s, n) \<in> td_set t k \<longleftrightarrow> (\<exists>n'. (s, n') \<in> td_set t 0 \<and> n = n' + k) "
  by (metis add.commute le_Suc_ex td_set_offset_0_conv td_set_offset_le'(1))


lemma td_set_list_set_td_set1: "(s, n) \<in> td_set_list ts k \<Longrightarrow>
  (\<exists>t n'. t \<in> set ts \<and> (s, n') \<in> td_set (dt_fst t) 0)"
  apply (induct ts arbitrary: n k)
   apply simp
  apply simp
  by (metis dt_tuple.collapse td_set_offset_0_conv' ts5)

lemma export_uinfo_size [simp]:
  "size_td (export_uinfo t) = size_td (t::('a,'b) typ_info)"
  by (simp add: export_uinfo_def)

lemma (in c_type) typ_uinfo_size [simp]:
  "size_td (typ_uinfo_t TYPE('a)) = size_td (typ_info_t TYPE('a))"
  by (simp add: typ_uinfo_t_def export_uinfo_def)

lemma wf_size_desc_map:
  shows "wf_size_desc (map_td f g t) = wf_size_desc t" and
        "wf_size_desc_struct (map_td_struct f g st) = wf_size_desc_struct st" and
        "wf_size_desc_list (map_td_list f g ts) = wf_size_desc_list ts" and
        "wf_size_desc_tuple (map_td_tuple f g x) = wf_size_desc_tuple x"
proof (induction t and st and ts and x)
  case (TypAggregate list)
  then show ?case by (cases list) auto
qed auto

lemma map_td_flr_Some [simp]:
  "map_td_flr f g (Some (t,n)) = Some (map_td f g t,n)"
  by (clarsimp simp: map_td_flr_def)

lemma map_td_flr_None [simp]:
  "map_td_flr f g None = None"
  by (clarsimp simp: map_td_flr_def)

lemma field_lookup_map:
  shows "\<And>f m s. field_lookup t f m = s \<Longrightarrow>
            field_lookup (map_td fupd g t) f m = map_td_flr fupd g s" and
        "\<And>f m s. field_lookup_struct st f m = s \<Longrightarrow>
            field_lookup_struct (map_td_struct fupd g st) f m = map_td_flr fupd g s" and
        "\<And>f m s. field_lookup_list ts f m = s \<Longrightarrow>
            field_lookup_list (map_td_list fupd g ts) f m = map_td_flr fupd g s" and
        "\<And>f m s. field_lookup_tuple x f m = s \<Longrightarrow>
            field_lookup_tuple (map_td_tuple fupd g x) f m = map_td_flr fupd g s"
proof (induct t and st and ts and x)
  case (Cons_typ_desc x xs) thus ?case
    by (clarsimp, cases x, auto simp: map_td_flr_def split: option.splits)
qed auto

lemma field_lookup_export_uinfo_Some:
  "field_lookup (t::('a,'b) typ_info) f m = Some (s,n) \<Longrightarrow>
      field_lookup (export_uinfo t) f m = Some (export_uinfo s,n)"
  by (simp add: export_uinfo_def field_lookup_map)

lemma field_lookup_struct_export_Some:
  "field_lookup_struct (st::('a,'b) typ_struct) f m = Some (s,n) \<Longrightarrow>
      field_lookup_struct (map_td_struct fupd g st) f m = Some (map_td fupd g s,n)"
  by (simp add: field_lookup_map)

lemma field_lookup_struct_export_None:
  "field_lookup_struct (st::('a, 'b) typ_struct) f m = None \<Longrightarrow>
      field_lookup_struct (map_td_struct fupd g st) f m = None"
  by (simp add: field_lookup_map)

lemma field_lookup_list_export_Some:
  "field_lookup_list (ts::('a, 'b) typ_tuple list) f m = Some (s,n) \<Longrightarrow>
      field_lookup_list (map_td_list fupd g ts) f m = Some (map_td fupd g s,n)"
  by (simp add: field_lookup_map)

lemma field_lookup_list_export_None:
  "field_lookup_list (ts::('a, 'b) typ_tuple list) f m = None \<Longrightarrow>
      field_lookup_list (map_td_list fupd g ts) f m = None"
  by (simp add: field_lookup_map)

lemma field_lookup_tuple_export_Some:
  "field_lookup_tuple (x::('a, 'b) typ_tuple) f m = Some (s,n) \<Longrightarrow>
      field_lookup_tuple (map_td_tuple fupd g x) f m = Some (map_td fupd g s,n)"
  by (simp add: field_lookup_map)

lemma field_lookup_tuple_export_None:
  "field_lookup_tuple (x::('a, 'b) typ_tuple) f m = None \<Longrightarrow>
      field_lookup_tuple (map_td_tuple fupd g x) f m = None"
  by (simp add: field_lookup_map)

lemma import_flr_Some [simp]:
  "import_flr f g (Some (map_td f g t,n)) (Some (t,n))"
  by (clarsimp simp: import_flr_def)

lemma import_flr_None [simp]:
  "import_flr f g None None"
  by (clarsimp simp: import_flr_def)

lemma field_lookup_export_uinfo_rev'':
  "\<And>f m s. field_lookup (map_td fupd g t) f m = s \<Longrightarrow>
      import_flr fupd g s ((field_lookup t f m)::('a,'b) flr)"
  "\<And>f m s. field_lookup_struct (map_td_struct fupd g st) f m = s \<Longrightarrow>
      import_flr fupd g s ((field_lookup_struct st f m)::('a,'b) flr)"
  "\<And>f m s. field_lookup_list (map_td_list fupd g ts) f m = s \<Longrightarrow>
      import_flr fupd g s ((field_lookup_list ts f m)::('a,'b) flr)"
  "\<And>f m s. field_lookup_tuple (map_td_tuple fupd g x) f m = s \<Longrightarrow>
      import_flr fupd g s ((field_lookup_tuple x f m)::('a,'b)  flr)"
proof (induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by (clarsimp simp: import_flr_def export_uinfo_def)
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
  then show ?case
    apply clarsimp
    apply(clarsimp split: option.splits)
     apply(cases f, clarsimp+)
     apply(rule conjI, clarsimp)
      apply(cases dt_tuple, simp)
     apply clarsimp
     apply(drule field_lookup_tuple_export_Some [where fupd=fupd and g=g])
     apply simp
    apply(rule conjI; clarsimp)
     apply(drule field_lookup_tuple_export_None [where fupd=fupd and g=g])
     apply simp
    apply metis
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by (auto)
qed



lemma field_lookup_export_uinfo_rev':
  "(\<forall>f m s. field_lookup (map_td fupd g t) f m = s \<longrightarrow>
      import_flr fupd g s ((field_lookup t f m)::('a,'b) flr)) \<and>
   (\<forall>f m s. field_lookup_struct (map_td_struct fupd g st) f m = s \<longrightarrow>
      import_flr fupd g s ((field_lookup_struct st f m)::('a,'b) flr)) \<and>
   (\<forall>f m s. field_lookup_list (map_td_list fupd g ts) f m = s \<longrightarrow>
      import_flr fupd g s ((field_lookup_list ts f m)::('a,'b) flr)) \<and>
   (\<forall>f m s. field_lookup_tuple (map_td_tuple fupd g x) f m = s \<longrightarrow>
      import_flr fupd g s ((field_lookup_tuple x f m)::('a,'b)  flr))"
  by (auto simp: field_lookup_export_uinfo_rev'')


lemma field_lookup_export_uinfo_Some_rev:
  "field_lookup (export_uinfo (t::('a,'b) typ_info)) f m = Some (s,n) \<Longrightarrow>
      \<exists>k. field_lookup t f m = Some (k,n) \<and> export_uinfo k = s"
  apply(insert field_lookup_export_uinfo_rev' [of field_norm "(\<lambda>_. ())" t undefined undefined undefined])
  apply clarsimp
  apply(drule spec [where x=f])
  apply(drule spec [where x=m])
  apply(clarsimp simp: import_flr_def export_uinfo_def split: option.splits)
  done

lemma (in c_type) field_lookup_uinfo_Some_rev:
  "field_lookup (typ_uinfo_t (TYPE('a))) f m = Some (s,n) \<Longrightarrow>
      \<exists>k. field_lookup (typ_info_t (TYPE('a))) f m = Some (k,n) \<and> export_uinfo k = s"
  apply (simp add: typ_uinfo_t_def)
  apply (rule field_lookup_export_uinfo_Some_rev)
  apply assumption
  done

lemma (in c_type) field_lookup_offset_untyped_eq [simp]:
  "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s,n) \<Longrightarrow>
      field_offset_untyped (typ_uinfo_t TYPE('a)) f = n"
  apply(simp add: field_offset_untyped_def typ_uinfo_t_def)
  apply(drule field_lookup_export_uinfo_Some)
  apply(simp add: typ_uinfo_t_def export_uinfo_def)
  done

lemma (in c_type) field_lookup_offset_eq [simp]:
  "field_lookup (typ_info_t TYPE('a)) f 0 = Some (s,n) \<Longrightarrow>
      field_offset TYPE('a) f = n"
  by(simp add: field_offset_def)

lemma field_offset_self [simp]:
  "field_offset t [] = 0"
  by (simp add: field_offset_def field_offset_untyped_def)

lemma (in c_type) field_ti_self [simp]:
  "field_ti TYPE('a) [] = Some (typ_info_t TYPE('a))"
  by (simp add: field_ti_def)

lemma (in c_type) field_size_self [simp]:
  "field_size TYPE('a) [] = size_td (typ_info_t TYPE('a))"
  by (simp add: field_size_def)


lemma field_lookup_prefix_None'':
  "(\<forall>f g m. field_lookup (t::('a,'b) typ_desc) f m = None \<longrightarrow> field_lookup t (f@g) m = None)"
  "(\<forall>f g m. field_lookup_struct (st::('a,'b) typ_struct) f m = None \<longrightarrow> f \<noteq> [] \<longrightarrow>
      field_lookup_struct st (f@g) m = None)"
  "(\<forall>f g m. field_lookup_list (ts::('a,'b) typ_tuple list) f m = None \<longrightarrow> f \<noteq> [] \<longrightarrow>
      field_lookup_list ts (f@g) m = None)"
  "(\<forall>f g m. field_lookup_tuple (x::('a,'b) typ_tuple) f m = None \<longrightarrow> f \<noteq> [] \<longrightarrow>
      field_lookup_tuple x (f@g) m = None)"
  by (induct t and st and ts and x)
     (clarsimp split: option.splits)+

lemma field_lookup_prefix_None':
  "(\<forall>f g m. field_lookup (t::('a,'b) typ_desc) f m = None \<longrightarrow> field_lookup t (f@g) m = None) \<and>
   (\<forall>f g m. field_lookup_struct (st::('a,'b) typ_struct) f m = None \<longrightarrow> f \<noteq> [] \<longrightarrow>
      field_lookup_struct st (f@g) m = None) \<and>
   (\<forall>f g m. field_lookup_list (ts::('a,'b) typ_tuple list) f m = None \<longrightarrow> f \<noteq> [] \<longrightarrow>
      field_lookup_list ts (f@g) m = None) \<and>
   (\<forall>f g m. field_lookup_tuple (x::('a,'b) typ_tuple) f m = None \<longrightarrow> f \<noteq> [] \<longrightarrow>
      field_lookup_tuple x (f@g) m = None)"
  by (auto simp: field_lookup_prefix_None'')

lemma field_lookup_prefix_Some'':
  "(\<forall>f g t' m n. field_lookup t f m = Some ((t'::('a,'b) typ_desc),n) \<longrightarrow> wf_desc t \<longrightarrow>
      field_lookup t (f@g) m = field_lookup t' g n)"
  "(\<forall>f g t' m n. field_lookup_struct st f m = Some ((t'::('a,'b) typ_desc),n) \<longrightarrow> wf_desc_struct st \<longrightarrow>
      field_lookup_struct st (f@g) m = field_lookup t' g n)"
  "(\<forall>f g t' m n. field_lookup_list ts f m = Some ((t'::('a,'b) typ_desc),n) \<longrightarrow> wf_desc_list ts \<longrightarrow>
      field_lookup_list ts (f@g) m = field_lookup t' g n)"
  "(\<forall>f g t' m n. field_lookup_tuple x f m = Some ((t'::('a,'b) typ_desc),n) \<longrightarrow> wf_desc_tuple x \<longrightarrow>
      field_lookup_tuple x (f@g) m = field_lookup t' g n)"
proof(induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by auto
next
  case (TypScalar nat1 nat2 a)
  then show ?case by auto
next
  case (TypAggregate list)
  then show ?case by auto
next
  case Nil_typ_desc
  then show ?case  by auto
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case  
    apply(clarsimp split: option.splits)
    apply(cases dt_tuple)
    subgoal for f
    apply(cases f, clarsimp)
      by (clarsimp simp: field_lookup_list_None split: if_split_asm)
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case  by auto
qed


lemma field_lookup_prefix_Some':
  "(\<forall>f g t' m n. field_lookup t f m = Some ((t'::('a, 'b) typ_desc),n) \<longrightarrow> wf_desc t \<longrightarrow>
      field_lookup t (f@g) m = field_lookup t' g n) \<and>
   (\<forall>f g t' m n. field_lookup_struct st f m = Some ((t'::('a,'b) typ_desc),n) \<longrightarrow> wf_desc_struct st \<longrightarrow>
      field_lookup_struct st (f@g) m = field_lookup t' g n) \<and>
   (\<forall>f g t' m n. field_lookup_list ts f m = Some ((t'::('a,'b) typ_desc),n) \<longrightarrow> wf_desc_list ts \<longrightarrow>
      field_lookup_list ts (f@g) m = field_lookup t' g n) \<and>
   (\<forall>f g t' m n. field_lookup_tuple x f m = Some ((t'::('a,'b) typ_desc),n) \<longrightarrow> wf_desc_tuple x \<longrightarrow>
      field_lookup_tuple x (f@g) m = field_lookup t' g n)"
  by (auto simp: field_lookup_prefix_Some'')

lemma field_lookup_append_eq:
  "wf_desc t \<Longrightarrow>
    field_lookup t (f @ g) n =
    Option.bind (field_lookup t f n) (\<lambda>(t', m). field_lookup t' g m)"
  by (cases "field_lookup t f n")
     (auto simp add: field_lookup_prefix_None''(1)[rule_format]
                     field_lookup_prefix_Some''(1)[rule_format])

lemma field_lookup_offset_shift:
  "NO_MATCH 0 m \<Longrightarrow> field_lookup t f 0 = Some (t', n) \<Longrightarrow> field_lookup t f m = Some (t', m + n)"
  by (simp add: field_lookup_offset)

lemma field_lookup_offset_shift':
  "field_lookup t f m = Some (s, k) \<Longrightarrow> field_lookup t f n = Some (s, k + n - m)"
  by (metis CTypes.field_lookup_offset2 Nat.add_diff_assoc2 add.commute field_lookup_offset
            field_lookup_offset_le(1))

lemma field_lookup_append:
  assumes t: "wf_desc t"
    and f: "field_lookup t f n = Some (u, m)" and g: "field_lookup u g l = Some (v, k)"
  shows "field_lookup t (f @ g) n = Some (v, k + m - l)"
  using field_lookup_prefix_Some''(1)[rule_format, OF f t, of g]
    g[THEN field_lookup_offset_shift', of m]
  by simp

lemma field_lvalue_empty_simp [simp]:
  "Ptr &(p\<rightarrow>[]) = p"
  by (simp add: field_lvalue_def field_offset_def field_offset_untyped_def)

lemma map_td_align [simp]:
  "align_td_wo_align (map_td f g t) = align_td_wo_align (t::('a,'b) typ_desc)"
  "align_td_wo_align_struct (map_td_struct f g st) = align_td_wo_align_struct (st::('a,'b) typ_struct)"
  "align_td_wo_align_list (map_td_list f g ts) = align_td_wo_align_list (ts::('a,'b) typ_tuple list)"
  "align_td_wo_align_tuple (map_td_tuple f g x) = align_td_wo_align_tuple (x::('a,'b) typ_tuple)"
  by (induct t and st and ts and x) auto

lemma map_td_align' [simp]:
  "align_td (map_td f g t) = align_td (t::('a,'b) typ_desc)"
  "align_td_struct (map_td_struct f g st) = align_td_struct (st::('a,'b) typ_struct)"
  "align_td_list (map_td_list f g ts) = align_td_list (ts::('a,'b) typ_tuple list)"
  "align_td_tuple (map_td_tuple f g x) = align_td_tuple (x::('a,'b) typ_tuple)"
  by (induct t and st and ts and x) auto

lemma typ_uinfo_align [simp]:
  "align_td_wo_align (export_uinfo t) = align_td_wo_align (t::('a,'b) typ_info)"
  by (simp add: export_uinfo_def)

lemma ptr_aligned_Ptr_0 [simp]:
  "ptr_aligned NULL"
  by (simp add: ptr_aligned_def)

lemma td_set_self [simp]:
  "(t,m) \<in> td_set t m"
  by (cases t) simp

lemma td_set_wf_size_desc [rule_format]:
  "(\<forall>s m n. wf_size_desc t \<longrightarrow> ((s::('a,'b) typ_desc),m) \<in> td_set t n \<longrightarrow> wf_size_desc s)"
  "(\<forall>s m n. wf_size_desc_struct st \<longrightarrow> ((s::('a,'b) typ_desc),m) \<in> td_set_struct st n \<longrightarrow> wf_size_desc s)"
  "(\<forall>s m n. wf_size_desc_list ts \<longrightarrow> ((s::('a,'b) typ_desc),m) \<in> td_set_list ts n \<longrightarrow> wf_size_desc s)"
  "(\<forall>s m n. wf_size_desc_tuple x \<longrightarrow> ((s::('a,'b) typ_desc),m) \<in> td_set_tuple x n \<longrightarrow> wf_size_desc s)"
  by (induct t and st and ts and x) force+

lemma td_set_size_lte':
  "(\<forall>s k m. ((s::('a,'b) typ_desc),k) \<in> td_set t m \<longrightarrow> size s = size t \<and> s=t \<and> k=m \<or> size s < size t)"
  "(\<forall>s k m. ((s::('a,'b) typ_desc),k) \<in> td_set_struct st m \<longrightarrow> size s < size st)"
  "(\<forall>s k m. ((s::('a,'b) typ_desc),k) \<in> td_set_list xs m \<longrightarrow> size s < size_list (size_dt_tuple size (\<lambda>_. 0) (\<lambda>_. 0)) xs)"
  "(\<forall>s k m. ((s::('a,'b) typ_desc),k) \<in> td_set_tuple x m \<longrightarrow> size s < size_dt_tuple size (\<lambda>_. 0) (\<lambda>_. 0) x)"
  by (induct t and st and xs and x) force+

lemma td_set_size_lte:
  "(s,k) \<in> td_set t m \<Longrightarrow> size s = size t \<and> s=t \<and> k=m \<or>
      size s < size t"
  by (simp add: td_set_size_lte')

lemma td_set_struct_size_lte:
  "(s,k) \<in> td_set_struct st m \<Longrightarrow> size s < size st"
  by (simp add: td_set_size_lte')

lemma td_set_list_size_lte:
  "(s,k) \<in> td_set_list ts m \<Longrightarrow> size s < size_list (size_dt_tuple size (\<lambda>_. 0) (\<lambda>_. 0)) ts"
  by (simp add: td_set_size_lte')

lemma td_aggregate_not_in_td_set_list [simp]:
  "\<not> (TypDesc algn (TypAggregate xs) tn,k) \<in> td_set_list xs m"
  by (fastforce dest: td_set_list_size_lte simp: size_char_def)

lemma sub_size_td:
  "(s::('a,'b) typ_desc) \<le> t \<Longrightarrow> size s \<le> size t"
  by (fastforce dest: td_set_size_lte simp: typ_tag_le_def)

lemma sub_tag_antisym:
  "\<lbrakk> (s::('a,'b) typ_desc) \<le> t; t \<le> s \<rbrakk> \<Longrightarrow> s=t"
  apply(frule sub_size_td)
  apply(frule sub_size_td [where t=s])
  apply(clarsimp simp: typ_tag_le_def)
  apply(drule td_set_size_lte)
  apply clarsimp
  done

lemma sub_tag_refl:
  "(s::('a,'b) typ_desc) \<le> s"
  unfolding typ_tag_le_def by (cases s, fastforce)

lemma sub_tag_sub':
  "\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set t m \<longrightarrow> td_set s n \<subseteq> td_set t m"
  "\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set_struct ts m \<longrightarrow> td_set s n \<subseteq> td_set_struct ts m"
  "\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set_list xs m \<longrightarrow> td_set s n \<subseteq> td_set_list xs m"
  "\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set_tuple x m \<longrightarrow> td_set s n \<subseteq> td_set_tuple x m"
  by (induct t and ts and xs and x) fastforce+

lemma sub_tag_sub:
  "(s,n) \<in> td_set t m \<Longrightarrow> td_set s n \<subseteq> td_set t m"
  by (simp add: sub_tag_sub')

lemma td_set_fst:
  "\<forall>m n. fst ` td_set (s::('a, 'b) typ_desc) m = fst ` td_set s n"
  "\<forall>m n. fst ` td_set_struct (st::('a,'b) typ_struct) m = fst ` td_set_struct st n"
  "\<forall>m n. fst ` td_set_list (xs::('a, 'b) typ_tuple list) m = fst ` td_set_list xs n"
  "\<forall>m n. fst ` td_set_tuple (x::('a, 'b) typ_tuple) m = fst ` td_set_tuple x n"
  by (induct s and st and xs and x) (all \<open>clarsimp\<close>, fast, fast)

lemma sub_tag_trans:
  "\<lbrakk> (s::('a,'b) typ_desc) \<le> t; t \<le> u \<rbrakk> \<Longrightarrow> s \<le> u"
  apply(clarsimp simp: typ_tag_le_def)
  by (meson sub_tag_sub'(1) subset_iff td_set_offset_0_conv)

(*fixme: move*)
instantiation typ_desc :: (type, type) order
begin
instance
  apply intro_classes
     apply(fastforce simp: typ_tag_lt_def typ_tag_le_def dest: td_set_size_lte)
    apply(rule sub_tag_refl)
   apply(erule (1) sub_tag_trans)
  apply(erule (1) sub_tag_antisym)
  done
end

lemma td_set_offset_size'':
  "\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set t m  \<longrightarrow> size_td s + (n - m) \<le> size_td t"
  "\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set_struct st m \<longrightarrow> size_td s + (n - m) \<le> size_td_struct st"
  "\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set_list ts m \<longrightarrow> size_td s + (n - m) \<le> size_td_list ts"
  "\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set_tuple x m \<longrightarrow> size_td s + (n - m) \<le> size_td_tuple x"
proof (induct t and st and ts and x)
  case (Cons_typ_desc dt_tuple list)
  then show ?case  
    apply (cases dt_tuple) 
    apply fastforce
    done
qed auto

lemma td_set_offset_size':
  "(\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set t m  \<longrightarrow> size_td s + (n - m) \<le> size_td t) \<and>
    (\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set_struct st m \<longrightarrow> size_td s + (n - m) \<le> size_td_struct st) \<and>
    (\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set_list ts m \<longrightarrow> size_td s + (n - m) \<le> size_td_list ts) \<and>
    (\<forall>s m n. ((s::('a,'b) typ_desc),n) \<in> td_set_tuple x m \<longrightarrow> size_td s + (n - m) \<le> size_td_tuple x)"
  by (auto simp: td_set_offset_size'')

lemma td_set_offset_size:
  "(s,n) \<in> td_set t 0 \<Longrightarrow> size_td s + n \<le> size_td t"
  using td_set_offset_size' [of t undefined undefined undefined] by fastforce

lemma td_set_struct_offset_size:
  "(s,n) \<in> td_set_struct st m \<Longrightarrow> size_td s + (n - m) \<le> size_td_struct st"
  using td_set_offset_size' [of undefined st undefined undefined] by clarsimp

lemma td_set_list_offset_size:
  "(s,n) \<in> td_set_list ts 0 \<Longrightarrow> size_td s + n \<le> size_td_list ts"
  using td_set_offset_size' [of undefined undefined ts undefined]
  by fastforce

lemma td_set_offset_size_m:
  "(s,n) \<in> td_set t m \<Longrightarrow> size_td s + (n - m) \<le> size_td t"
  using insert td_set_offset_size' [of t undefined undefined undefined]
  by clarsimp

lemma td_set_list_offset_size_m:
  "(s,n) \<in> td_set_list t m \<Longrightarrow> size_td s + (n - m) \<le> size_td_list t"
  using insert td_set_offset_size' [of undefined undefined t undefined]
  by clarsimp

lemma td_set_tuple_offset_size_m:
  "(s,n) \<in> td_set_tuple t m \<Longrightarrow> size_td s + (n - m) \<le> size_td_tuple t"
  using td_set_offset_size' [of undefined undefined undefined t]
  by clarsimp



lemma td_set_list_offset_le:
  "(s,n) \<in> td_set_list ts m \<Longrightarrow> m \<le> n"
  by (simp add: td_set_offset_le')

lemma td_set_tuple_offset_le:
  "(s,n) \<in> td_set_tuple ts m \<Longrightarrow> m \<le> n"
  by (simp add: td_set_offset_le')

lemma field_of_self [simp]:
  "field_of 0 t t"
  by (simp add: field_of_def)

lemma td_set_export_uinfo':
  "\<forall>f m n s. ((s::('a,'b) typ_info),n) \<in> td_set t m \<longrightarrow>
     (export_uinfo s,n) \<in> td_set (export_uinfo t) m"
  "\<forall>f m n s. ((s::('a,'b) typ_info),n) \<in> td_set_struct st m \<longrightarrow>
     (export_uinfo s,n) \<in> td_set_struct (map_td_struct field_norm (\<lambda>_. ()) st) m"
  "\<forall>f m n s. ((s::('a,'b) typ_info),n) \<in> td_set_list ts m \<longrightarrow>
     (export_uinfo s,n) \<in> td_set_list (map_td_list field_norm (\<lambda>_. ()) ts) m"
  "\<forall>f m n s. ((s::('a,'b) typ_info),n) \<in> td_set_tuple x m \<longrightarrow>
     (export_uinfo s,n) \<in> td_set_tuple (map_td_tuple field_norm (\<lambda>_. ()) x) m"
proof (induct t and st and ts and x)
  case (Cons_typ_desc dt_tuple list)
  then show ?case by(cases dt_tuple) (simp add: export_uinfo_def)
qed (auto simp add: export_uinfo_def)

lemma td_set_export_uinfo:
  "(\<forall>f m n s. ((s::('a,'b) typ_info),n) \<in> td_set t m \<longrightarrow>
      (export_uinfo s,n) \<in> td_set (export_uinfo t) m) \<and>
   (\<forall>f m n s. ((s::('a,'b) typ_info),n) \<in> td_set_struct st m \<longrightarrow>
      (export_uinfo s,n) \<in> td_set_struct (map_td_struct field_norm (\<lambda>_. ()) st) m) \<and>
   (\<forall>f m n s. ((s::('a,'b) typ_info),n) \<in> td_set_list ts m \<longrightarrow>
      (export_uinfo s,n) \<in> td_set_list (map_td_list field_norm (\<lambda>_. ()) ts) m) \<and>
   (\<forall>f m n s. ((s::('a,'b) typ_info),n) \<in> td_set_tuple x m \<longrightarrow>
      (export_uinfo s,n) \<in> td_set_tuple (map_td_tuple field_norm (\<lambda>_. ()) x) m)"
  by (auto simp: td_set_export_uinfo')


lemma td_set_export_uinfoD:
  "(s,n) \<in> td_set t m \<Longrightarrow> (export_uinfo s,n) \<in> td_set (export_uinfo t) m"
  using td_set_export_uinfo [of t undefined undefined undefined] by clarsimp

lemma td_set_field_lookup'':
  "\<forall>s m n. wf_desc t \<longrightarrow> (((s::('a,'b) typ_desc),m + n) \<in> td_set t m \<longrightarrow>
     (\<exists>f. field_lookup t f m = Some (s,m+n)))"
  "\<forall>s m n. wf_desc_struct st \<longrightarrow> (((s::('a,'b) typ_desc),m + n) \<in> td_set_struct st m \<longrightarrow>
     (\<exists>f. field_lookup_struct st f m = Some (s,m+n)))"
  "\<forall>s m n. wf_desc_list ts \<longrightarrow> (((s::('a,'b) typ_desc),m + n) \<in> td_set_list ts m \<longrightarrow>
     (\<exists>f. field_lookup_list ts f m = Some (s,m+n)))"
  "\<forall>s m n. wf_desc_tuple x \<longrightarrow> (((s::('a,'b) typ_desc),m + n) \<in> td_set_tuple x m \<longrightarrow>
     (\<exists>f. field_lookup_tuple x f m = Some (s,m+n)))"
proof (induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case    
    apply clarsimp
    subgoal for s m n
      apply(cases s, clarsimp)
      apply (rule conjI)
       apply clarsimp
       apply(rule exI [where x="[]"])
       apply clarsimp+
      apply((erule allE)+, erule (1) impE)
      apply clarsimp
      subgoal for _ _ _ f
        apply(cases f, clarsimp+)
        subgoal for x xs
          apply(rule exI [where x="x#xs"])
          apply clarsimp
          done
        done
      done
    done
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
  then show ?case 
    apply clarsimp
    apply(rule conjI, clarsimp)
     apply((erule allE)+, erule (1) impE)
     apply(clarsimp) 

    subgoal for s m n f
      apply (cases f, clarsimp+)
      subgoal for x xs
        apply(rule exI [where x="x#xs"])
        apply(clarsimp)
        done
      done
    apply clarsimp
    subgoal premises prems for s m n
      using prems(1-3,6 ) 
        prems(5)[rule_format, of s "m + size_td (dt_fst dt_tuple)" "n - size_td (dt_fst dt_tuple)"]
      apply -
      apply(frule td_set_list_offset_le)
      apply clarsimp
      subgoal for f
        apply(rule exI [where x=f])
        apply(clarsimp split: option.splits)
        apply(cases dt_tuple, clarsimp split: if_split_asm)
        apply(cases f, clarsimp+)
        apply(simp add: field_lookup_list_None)
        done
      done
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case   
    apply clarsimp
    apply((erule allE)+, erule (1) impE)
    apply clarsimp
    subgoal for s m n f
      apply(rule exI [where x="list#f"])
      apply clarsimp
      done
    done
qed

lemma td_set_field_lookup':
  "(\<forall>s m n. wf_desc t \<longrightarrow> (((s::('a,'b) typ_desc),m + n) \<in> td_set t m \<longrightarrow>
      (\<exists>f. field_lookup t f m = Some (s,m+n)))) \<and>
    (\<forall>s m n. wf_desc_struct st \<longrightarrow> (((s::('a,'b) typ_desc),m + n) \<in> td_set_struct st m \<longrightarrow>
      (\<exists>f. field_lookup_struct st f m = Some (s,m+n)))) \<and>
    (\<forall>s m n. wf_desc_list ts \<longrightarrow> (((s::('a,'b) typ_desc),m + n) \<in> td_set_list ts m \<longrightarrow>
      (\<exists>f. field_lookup_list ts f m = Some (s,m+n)))) \<and>
    (\<forall>s m n. wf_desc_tuple x \<longrightarrow> (((s::('a,'b) typ_desc),m + n) \<in> td_set_tuple x m \<longrightarrow>
      (\<exists>f. field_lookup_tuple x f m = Some (s,m+n))))"
  by (auto simp: td_set_field_lookup'')


lemma td_set_field_lookup_rev'':
  "\<forall>s m n. (\<exists>f. field_lookup t f m = Some (s,m+n)) \<longrightarrow>
     ((s::('a,'b) typ_desc),m + n) \<in> td_set t m"
  "\<forall>s m n. (\<exists>f. field_lookup_struct st f m = Some (s,m+n)) \<longrightarrow>
     ((s::('a,'b) typ_desc),m + n) \<in> td_set_struct st m"
  "\<forall>s m n. (\<exists>f. field_lookup_list ts f m = Some (s,m+n)) \<longrightarrow>
     ((s::('a,'b) typ_desc),m + n) \<in> td_set_list ts m"
  "\<forall>s m n. (\<exists>f. field_lookup_tuple x f m = Some (s,m+n)) \<longrightarrow>
     ((s::('a,'b) typ_desc),m + n) \<in> td_set_tuple x m"
proof(induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case        
    apply clarsimp
    subgoal for s m n f
      apply(cases f, clarsimp)
      apply clarsimp
      apply((erule allE)+, erule impE, fast)
      apply fast
      done
    done
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
  then show ?case  
    apply clarsimp
    apply(clarsimp split: option.splits)
    subgoal premises prems for s m n f
      using prems (1, 4-5)
        prems(3)[rule_format, where s = s and m = "m + size_td (dt_fst dt_tuple)" and n= "n - size_td (dt_fst dt_tuple)"]
      apply -

      apply(frule field_lookup_offset_le)
      apply clarsimp
      apply fast
      done
    subgoal by auto 
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case   
    apply clarsimp
    subgoal for s m n f
      apply(cases f, clarsimp+)
      apply((erule allE)+, erule impE, fast)
      apply assumption
      done
    done
qed

lemma td_set_field_lookup_rev':
  "(\<forall>s m n. (\<exists>f. field_lookup t f m = Some (s,m+n)) \<longrightarrow>
      ((s::('a,'b) typ_desc),m + n) \<in> td_set t m) \<and>
    (\<forall>s m n. (\<exists>f. field_lookup_struct st f m = Some (s,m+n)) \<longrightarrow>
      ((s::('a,'b) typ_desc),m + n) \<in> td_set_struct st m) \<and>
    (\<forall>s m n. (\<exists>f. field_lookup_list ts f m = Some (s,m+n)) \<longrightarrow>
      ((s::('a,'b) typ_desc),m + n) \<in> td_set_list ts m) \<and>
    (\<forall>s m n. (\<exists>f. field_lookup_tuple x f m = Some (s,m+n)) \<longrightarrow>
      ((s::('a,'b) typ_desc),m + n) \<in> td_set_tuple x m)"
  by (auto simp: td_set_field_lookup_rev'')

lemma td_set_field_lookup:
  "wf_desc t \<Longrightarrow> k \<in> td_set t 0 = (\<exists>f. field_lookup t f 0 = Some k)"
  using td_set_field_lookup' [of t undefined undefined undefined]
        td_set_field_lookup_rev' [of t undefined undefined undefined]
  apply clarsimp
  apply(cases k, clarsimp)
  by (metis add_0)

lemma td_set_field_lookupD:
  "field_lookup t f m = Some k \<Longrightarrow> k \<in> td_set t m"
  using td_set_field_lookup_rev' [of t undefined undefined undefined]
  apply(cases k, clarsimp)
  by (metis field_lookup_offset_le(1) le_iff_add)

lemma td_set_struct_field_lookup_structD:
  "field_lookup_struct st f m = Some k \<Longrightarrow> k \<in> td_set_struct st m"
  using td_set_field_lookup_rev' [of undefined st undefined undefined]
  apply(cases k, clarsimp)
  by (metis field_lookup_offset_le(2) le_iff_add)

lemma field_lookup_struct_td_simp [simp]:
  "field_lookup_struct ts f m \<noteq> Some (TypDesc algn ts nm, m)"
  by (fastforce dest: td_set_struct_field_lookup_structD td_set_struct_size_lte)


lemma td_set_list_field_lookup_listD:
  "field_lookup_list xs f m = Some k \<Longrightarrow> k \<in> td_set_list xs m"
  using td_set_field_lookup_rev' [of undefined undefined xs undefined]
  apply(cases k, clarsimp)
  by (metis field_lookup_offset_le(3) le_Suc_ex)

lemma td_set_tuple_field_lookup_tupleD:
  "field_lookup_tuple x f m = Some k \<Longrightarrow> k \<in> td_set_tuple x m"
  using td_set_field_lookup_rev' [of undefined undefined undefined x]
  apply(cases k, clarsimp)
  by (metis field_lookup_offset_le(4) nat_le_iff_add)

lemma field_lookup_offset_size'':
  "field_lookup t f n = Some (u, m) \<Longrightarrow> size_td u + m \<le> size_td t + n"
  by (metis Nat.add_diff_assoc field_lookup_offset_le(1)
            le_diff_conv td_set_field_lookupD td_set_offset_size')

lemma field_lookup_offset_size':
  assumes n: "field_lookup t f 0 = Some (t',n)" shows "size_td t' + n \<le> size_td t"
  using field_lookup_offset_size''[OF n] by simp

lemma intvl_subset_of_field_lookup:
  "field_lookup t f 0 = Some (u, n) \<Longrightarrow>
    {a + of_nat n ..+ size_td u} \<subseteq> {a ..+ size_td t}"
  by (simp add: field_lookup_offset_size' intvl_le)

lemma field_lookup_wf_size_desc_gt:
  "\<lbrakk> field_lookup t f n = Some (a,b); wf_size_desc t \<rbrakk> \<Longrightarrow> 0 < size_td a"
  by (fastforce simp: td_set_wf_size_desc wf_size_desc_gt dest!: td_set_field_lookupD)

lemma field_lookup_inject'':
  "\<forall>f g m s. wf_size_desc t \<longrightarrow> field_lookup (t::('a,'b) typ_desc) f m = Some s \<and> field_lookup t g m = Some s \<longrightarrow> f=g"
  "\<forall>f g m s. wf_size_desc_struct st \<longrightarrow> field_lookup_struct (st::('a,'b) typ_struct) f m = Some s \<and> field_lookup_struct  st g m = Some s \<longrightarrow> f=g"
  "\<forall>f g m s. wf_size_desc_list ts \<longrightarrow> field_lookup_list (ts::('a,'b) typ_tuple list) f m = Some s \<and> field_lookup_list ts g m = Some s \<longrightarrow> f=g"
  "\<forall>f g m s. wf_size_desc_tuple x \<longrightarrow> field_lookup_tuple (x::('a,'b) typ_tuple) f m = Some s \<and> field_lookup_tuple x g m = Some s \<longrightarrow> f=g"
proof(induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by clarsimp fast
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
  then show ?case 
    apply clarsimp
    subgoal for f g m a b
      apply(clarsimp split: option.splits)
         apply fast
      subgoal
        apply(frule td_set_tuple_field_lookup_tupleD)
        apply(drule field_lookup_offset_le)
        apply(drule td_set_tuple_offset_size_m)
        subgoal premises prems
          using prems(3-8)
          apply(cases dt_tuple, simp)
          subgoal premises prems
          proof -
            have "0 < size_td a"
              using prems
              apply -
              apply(clarsimp split: if_split_asm; drule (2) field_lookup_wf_size_desc_gt)
              done
            then show ?thesis
              using prems
              by simp
          qed
          done
        done
      subgoal
        apply(frule td_set_tuple_field_lookup_tupleD)
        apply(drule field_lookup_offset_le)
        apply(drule td_set_tuple_offset_size_m)
        subgoal premises prems
          using prems(3-8)
          apply(cases dt_tuple, simp)
          subgoal premises prems
          proof -
            have "0 < size_td a"
              using prems
              apply -
              apply(clarsimp split: if_split_asm; drule (2) field_lookup_wf_size_desc_gt)
              done
            then show ?thesis
              using prems
              by simp
          qed
          done
        done   
      subgoal by best
      done
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case 
    apply clarsimp
    subgoal for f g m a b
      apply(drule spec [where x="tl f"])
      apply(drule spec [where x="tl g"])
      apply(cases f; simp)
      apply(cases g; simp)
      apply fastforce
      done
    done
qed

lemma field_lookup_inject':
  "(\<forall>f g m s. wf_size_desc t \<longrightarrow> field_lookup (t::('a,'b) typ_desc) f m = Some s \<and> field_lookup t g m = Some s \<longrightarrow> f=g) \<and>
      (\<forall>f g m s. wf_size_desc_struct st \<longrightarrow> field_lookup_struct (st::('a,'b) typ_struct) f m = Some s \<and> field_lookup_struct  st g m = Some s \<longrightarrow> f=g) \<and>
      (\<forall>f g m s. wf_size_desc_list ts \<longrightarrow> field_lookup_list (ts::('a,'b) typ_tuple list) f m = Some s \<and> field_lookup_list ts g m = Some s \<longrightarrow> f=g) \<and>
      (\<forall>f g m s. wf_size_desc_tuple x \<longrightarrow> field_lookup_tuple (x::('a,'b) typ_tuple) f m = Some s \<and> field_lookup_tuple x g m = Some s \<longrightarrow> f=g)"
  by (auto simp: field_lookup_inject'')


lemma field_lookup_inject:
  "\<lbrakk> field_lookup (t::('a,'b) typ_desc) f m = Some s;
      field_lookup t g m = Some s; wf_size_desc t \<rbrakk> \<Longrightarrow> f=g"
  using field_lookup_inject' [of t undefined undefined undefined]
  apply(cases s)
  apply clarsimp
  apply(drule spec [where x=f])
  apply(drule spec [where x=g])
  apply fast
  done

lemma fd_cons_update_normalise:
  "\<lbrakk> fd_cons_update_access d n; fd_cons_access_update d n;
        fd_cons_double_update d; fd_cons_length d n \<rbrakk> \<Longrightarrow>
        fd_cons_update_normalise d n"
  apply(clarsimp simp: fd_cons_update_access_def fd_cons_update_normalise_def norm_desc_def)
  subgoal for v bs
    apply(drule spec [where x="field_update d bs v"])
    apply(drule spec [where x="replicate (length bs) 0"])
    apply clarsimp
    apply(clarsimp simp: fd_cons_access_update_def)
    apply(drule spec [where x=bs])
    apply clarsimp
    apply(drule spec [where x="replicate (length bs) 0"])
    apply clarsimp
    apply(drule spec [where x=v])
    apply(drule spec [where x=undefined])
    apply clarsimp
    apply(clarsimp simp: fd_cons_double_update_def)
    apply(drule spec [where x="v"])
    apply(drule spec [where x="field_access d (field_update d bs undefined)
                                    (replicate (length bs) 0)"])
    apply(drule spec [where x=bs])
    apply clarsimp
    apply(erule impE)
     apply(clarsimp simp: fd_cons_length_def)
    apply clarsimp
    done
  done

lemma update_ti_t_update_ti_struct_t [simp]:
  "update_ti_t (TypDesc algn st tn) = update_ti_struct_t st"
  by (auto simp: update_ti_t_def update_ti_struct_t_def)

lemma fd_cons_fd_cons_struct [simp]:
  "fd_cons (TypDesc algn st tn) = fd_cons_struct st"
  by (clarsimp simp: fd_cons_def fd_cons_struct_def)

lemma update_ti_struct_t_update_ti_list_t [simp]:
  "update_ti_struct_t (TypAggregate ts) = update_ti_list_t ts"
  by (auto simp: update_ti_struct_t_def update_ti_list_t_def)

lemma fd_cons_struct_fd_cons_list [simp]:
  "fd_cons_struct (TypAggregate ts) = fd_cons_list ts"
  by (clarsimp simp: fd_cons_struct_def fd_cons_list_def)

lemma fd_cons_list_empty [simp]:
  "fd_cons_list []"
  by (clarsimp simp: fd_cons_list_def fd_cons_double_update_def
    fd_cons_update_access_def fd_cons_access_update_def fd_cons_length_def
    fd_cons_update_normalise_def update_ti_list_t_def fd_cons_desc_def)

lemma fd_cons_double_update_list_append:
  "\<lbrakk> fd_cons_double_update (field_desc_list xs);
      fd_cons_double_update (field_desc_list ys);
      fu_commutes (field_update (field_desc_list xs)) (field_update (field_desc_list ys)) \<rbrakk> \<Longrightarrow>
      fd_cons_double_update (field_desc_list (xs@ys))"
  by (auto simp: fd_cons_double_update_def fu_commutes_def)

lemma fd_cons_update_access_list_append:
  "\<lbrakk> fd_cons_update_access (field_desc_list xs) (size_td_list xs);
      fd_cons_update_access (field_desc_list ys) (size_td_list ys);
      fd_cons_length (field_desc_list xs) (size_td_list xs);
      fd_cons_length (field_desc_list ys) (size_td_list ys) \<rbrakk> \<Longrightarrow>
      fd_cons_update_access (field_desc_list (xs@ys)) (size_td_list (xs@ys))"
 by (auto simp: fd_cons_update_access_def fd_cons_length_def access_ti_append)

(* fixme MOVE *)
lemma min_ll:
  "min (x + y) x = (x::nat)"
  by simp

lemma fd_cons_access_update_list_append:
  "\<lbrakk> fd_cons_access_update (field_desc_list xs) (size_td_list xs);
      fd_cons_access_update (field_desc_list ys) (size_td_list ys);
      fu_commutes (field_update (field_desc_list xs)) (field_update (field_desc_list ys)) \<rbrakk> \<Longrightarrow>
      fd_cons_access_update (field_desc_list (xs@ys)) (size_td_list (xs@ys))"
  apply(clarsimp simp: fd_cons_access_update_def)
  subgoal for bs bs' v v'
    apply(drule spec [where x="take (size_td_list xs) bs"])
    apply clarsimp
    apply(simp add: access_ti_append)
    apply(drule spec [where x="drop (size_td_list xs) bs"])
    apply clarsimp
    apply(drule spec [where x="take (size_td_list xs) bs'"])
    apply(simp add: min_ll)
    apply(drule spec [where x="update_ti_list_t ys (drop (size_td_list xs) bs) v"])
    apply(drule spec [where x="update_ti_list_t ys (drop (size_td_list xs) bs) v'"])
    apply simp
    apply(frule fu_commutes[where bs="take (size_td_list xs) bs" and
        bs'="drop (size_td_list xs) bs" and v=v ])
    apply clarsimp
    apply(frule fu_commutes[where bs="take (size_td_list xs) bs" and
        bs'="drop (size_td_list xs) bs" and v=v'])
    apply clarsimp
    done
  done

lemma fd_cons_length_list_append:
  "\<lbrakk> fd_cons_length (field_desc_list xs) (size_td_list xs);
     fd_cons_length (field_desc_list ys) (size_td_list ys) \<rbrakk> \<Longrightarrow>
   fd_cons_length (field_desc_list (xs@ys)) (size_td_list (xs@ys))"
  by (auto simp: fd_cons_length_def access_ti_append)

lemma wf_fdp_insert:
  "wf_fdp (insert x xs) \<Longrightarrow> wf_fdp {x} \<and> wf_fdp xs"
  by (auto simp: wf_fdp_def)

lemma wf_fdp_fd_cons:
  "\<lbrakk> wf_fdp X; (t,m) \<in> X \<rbrakk> \<Longrightarrow> fd_cons t"
  by (auto simp: wf_fdp_def)

lemma wf_fdp_fu_commutes:
  "\<lbrakk> wf_fdp X; (s,m) \<in> X; (t,n) \<in> X; \<not> m \<le> n; \<not> n \<le> m \<rbrakk> \<Longrightarrow>
      fu_commutes (field_update (field_desc s)) (field_update (field_desc t))"
  by (auto simp: wf_fdp_def)

lemma wf_fdp_fa_fu_ind:
  "\<lbrakk> wf_fdp X; (s,m) \<in> X; (t,n) \<in> X; \<not> m \<le> n; \<not> n \<le> m \<rbrakk> \<Longrightarrow>
      fa_fu_ind (field_desc s) (field_desc t) (size_td t) (size_td s)"
  by (auto simp: wf_fdp_def)

lemma wf_fdp_mono:
  "\<lbrakk> wf_fdp Y; X \<subseteq> Y \<rbrakk> \<Longrightarrow> wf_fdp X"
  by (fastforce simp: wf_fdp_def)

lemma tf0 [simp]:
  "tf_set (TypDesc algn st nm) = {(TypDesc algn st nm,[])} \<union> tf_set_struct st"
  by (auto simp: tf_set_def tf_set_struct_def)

lemma tf1 [simp]:  "tf_set_struct (TypScalar m algn d) = {}"
  by (clarsimp simp: tf_set_struct_def)

lemma tf2 [simp]:  "tf_set_struct (TypAggregate xs) = tf_set_list xs"
  by (auto simp: tf_set_struct_def tf_set_list_def)

lemma tf3 [simp]:  "tf_set_list [] = {}"
  by (simp add: tf_set_list_def)

lemma tf4:  "tf_set_list (x#xs) = tf_set_tuple x \<union> {t. t \<in> tf_set_list xs \<and> snd t \<notin>  snd ` tf_set_tuple x}"
  apply(clarsimp simp: tf_set_list_def tf_set_tuple_def)
  apply(cases x)
  apply clarsimp
  subgoal for x1 a b
    apply(rule equalityI; clarsimp)
    subgoal for a' b'
      apply(cases b'; clarsimp)
      apply(erule disjE; clarsimp?)
      apply(fastforce dest: field_lookup_list_offset2 split: option.splits)[1]
      done
    apply (rule conjI; clarsimp)
    subgoal for   _ ys n
      apply(cases ys; clarsimp split: option.splits)
      apply(rule conjI; clarsimp simp: image_def)
       apply(drule field_lookup_list_offset3[where  m="size_td x1"])
       apply fast
      apply(drule field_lookup_list_offset3[where  m="size_td x1"])
      apply fast
      done
    done
  done

lemma tf4D:
  "t \<in> tf_set_list (x#xs) \<Longrightarrow> t \<in> (tf_set_tuple x \<union> tf_set_list xs)"
  by (clarsimp simp: tf4)

lemma tf4' [simp]:  "wf_desc_list (x#xs) \<Longrightarrow>
  tf_set_list (x#xs) = tf_set_tuple x \<union> tf_set_list xs"
  apply(simp add: tf4)
  apply(rule equalityI; clarsimp)
  subgoal for _ _ ys
  apply(clarsimp simp: tf_set_tuple_def tf_set_list_def)
  apply(cases x, simp)
  apply(clarsimp split: if_split_asm)
    apply(cases ys; simp)
    subgoal for _ _ _ _ _ list
      apply(drule field_lookup_list_None [where fs=list and m=0])
      apply fastforce
      done
    done
  done

lemma tf5 [simp]:  "tf_set_tuple (DTuple t m d) = {(a,m#b) | a b. (a,b) \<in> tf_set t}"
  apply(clarsimp simp: tf_set_tuple_def tf_set_def)
  apply(rule equalityI; clarsimp)
  subgoal for _ xs n
  apply(cases xs; clarsimp)
    done
  done

lemma tf_set_self [simp]:
  "(t,[]) \<in> tf_set t"
  by (clarsimp simp: tf_set_def)


lemma tf_set_list_mem:
  "wf_desc_list ts \<Longrightarrow>  DTuple t n d \<in> set ts \<Longrightarrow> (t,[n]) \<in> tf_set_list ts"
  by (induct ts) auto

lemma tf_set_list_append:
  "wf_desc_list (xs@ys) \<Longrightarrow> tf_set_list (xs@ys) = tf_set_list xs \<union> tf_set_list ys"
  apply(induct xs; clarsimp)
  apply(subst tf4'; fastforce)
  done

lemma lf_set_list_append [simp]:
  "lf_set_list (xs@ys) fn = lf_set_list xs fn \<union> lf_set_list ys fn"
  by (induct xs) auto

lemma ti_ind_sym:
  "ti_ind X Y \<Longrightarrow> ti_ind Y X"
  by (auto simp: ti_ind_def fu_commutes_def)

lemma ti_ind_sym2:
  "ti_ind X Y = ti_ind Y X"
  by (blast dest: ti_ind_sym)

lemma ti_ind_list [simp]:
  "ti_ind (X \<union> Y) Z = (ti_ind X Z \<and> ti_ind Y Z)"
  unfolding ti_ind_def by auto

lemma ti_empty [simp]:
  "ti_ind {} X"
  by (simp add: ti_ind_def)

lemma wf_lf_list:
  "lf_fn ` X \<inter> lf_fn ` Y = {} \<Longrightarrow>
      wf_lf (X \<union> Y) = (wf_lf X \<and> wf_lf Y \<and> ti_ind X Y)"
  unfolding wf_lf_def ti_ind_def field_desc_def fu_commutes_def
  apply (rule iffI; clarsimp)
  subgoal for x y
   apply(frule spec [where x=x])
   apply(drule spec [where x=y])
   apply clarsimp
   apply(drule spec [where x=y])
   apply(drule spec [where x=x])
   apply clarsimp
    apply fastforce
    done
  subgoal by fast
  done

lemma wf_lf_listD:
  "wf_lf (X \<union> Y) \<Longrightarrow> wf_lf X \<and> wf_lf Y"
  unfolding wf_lf_def ti_ind_def field_desc_def fu_commutes_def by clarsimp

lemma ti_ind_fn:
  fixes t::"('a,'b) typ_info" and
    st::"('a,'b) typ_info_struct" and
    ts::"('a,'b) typ_info_tuple list" and
    x::"('a,'b) typ_info_tuple"
  shows
  "\<forall>fn. ti_ind (lf_set t fn) Y = ti_ind (lf_set t []) Y"
  "\<forall>fn. ti_ind (lf_set_struct st fn) Y = ti_ind (lf_set_struct st []) Y"
  "\<forall>fn. ti_ind (lf_set_list ts fn) Y = ti_ind (lf_set_list ts []) Y"
  "\<forall>fn. ti_ind (lf_set_tuple x fn) Y = ti_ind (lf_set_tuple x []) Y"
  apply(induct t and st and ts and x, all \<open>clarsimp\<close>)
    apply (fastforce simp: ti_ind_def)
   apply auto
  done

lemma ti_ind_ld_td':
  fixes t::"('a,'b) typ_info" and
    st::"('a,'b) typ_info_struct" and
    ts::"('a,'b) typ_info_tuple list" and
    x::"('a,'b) typ_info_tuple"
  shows
  "ti_ind (lf_set t []) Y \<longrightarrow> ti_ind {t2d (t,[])} Y"
  "ti_ind (lf_set_struct st []) Y \<longrightarrow> ti_ind {\<lparr> lf_fd = field_desc_struct st, lf_sz = size_td_struct st, lf_fn = [] \<rparr>} Y"
  "ti_ind (lf_set_list ts []) Y \<longrightarrow> ti_ind {\<lparr> lf_fd = field_desc_list ts, lf_sz = size_td_list ts, lf_fn = [] \<rparr>} Y"
  "ti_ind (lf_set_tuple x []) Y \<longrightarrow> ti_ind {\<lparr> lf_fd = field_desc_tuple x, lf_sz = size_td_tuple x, lf_fn = [] \<rparr>} Y"
  apply(induct t and st and ts and x, all \<open>clarsimp simp: t2d_def\<close>)
     apply((clarsimp simp: ti_ind_def fu_commutes_def fa_fu_ind_def)+)[3]
  apply(subst (asm) ti_ind_fn)
  apply simp
  done

lemma ti_ind_ld_td_struct:
  "ti_ind (lf_set_struct st fn) Y \<Longrightarrow>
   ti_ind {\<lparr> lf_fd = field_desc_struct st, lf_sz = size_td_struct st, lf_fn = [] \<rparr>} Y"
  by (subst (asm) ti_ind_fn) (simp only: ti_ind_ld_td')

lemma ti_ind_ld_td_list:
  "ti_ind (lf_set_list ts fn) Y \<Longrightarrow>
   ti_ind {\<lparr> lf_fd = field_desc_list ts, lf_sz = size_td_list ts, lf_fn = [] \<rparr>} Y"
  by (subst (asm) ti_ind_fn) (simp only: ti_ind_ld_td')

lemma ti_ind_ld_td_tuple:
  "ti_ind (lf_set_tuple x fn) Y \<Longrightarrow>
   ti_ind {\<lparr> lf_fd = field_desc_tuple x, lf_sz = size_td_tuple x, lf_fn = [] \<rparr>} Y"
  by (subst (asm) ti_ind_fn) (simp only: ti_ind_ld_td')

lemma ti_ind_ld':
  fixes t::"('a,'b) typ_info" and
    st::"('a,'b) typ_info_struct" and
    ts::"('a,'b) typ_info_tuple list" and
    x::"('a,'b) typ_info_tuple"
  shows
  "ti_ind (lf_set t []) Y \<longrightarrow> ti_ind (t2d ` (tf_set t)) Y"
  "ti_ind (lf_set_struct st []) Y \<longrightarrow> ti_ind (t2d ` (tf_set_struct st)) Y"
  "ti_ind (lf_set_list ts []) Y \<longrightarrow> ti_ind (t2d ` (tf_set_list ts)) Y"
  "ti_ind (lf_set_tuple x []) Y \<longrightarrow> ti_ind (t2d ` (tf_set_tuple x)) Y"
proof(induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case 
    apply clarsimp
    apply(frule ti_ind_ld_td_struct)
    apply(subst insert_def)
    apply(subst ti_ind_list)
    apply(clarsimp simp: ti_ind_def t2d_def)
    done
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
  then show ?case apply clarsimp
   apply(clarsimp simp: ti_ind_def t2d_def)
   apply(drule tf4D)
    apply clarsimp
    by (smt (verit, best) field_desc.select_convs(2) fst_eqD image_eqI 
        leaf_desc.select_convs(1) leaf_desc.select_convs(2))
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case 
    apply clarsimp
    apply(subst (asm) (2) ti_ind_fn)
    apply(simp add: t2d_def)
    apply(clarsimp simp: ti_ind_def)
    by (metis (mono_tags, lifting) field_desc.select_convs(2) fst_conv image_eqI 
        leaf_desc.select_convs(1) leaf_desc.select_convs(2))
qed

lemma ti_ind_ld:
  "ti_ind (lf_set t fn) Y \<Longrightarrow> ti_ind (t2d ` (tf_set t)) Y"
  by (subst (asm) ti_ind_fn) (simp only: ti_ind_ld')

lemma ti_ind_ld_struct:
  "ti_ind (lf_set_struct t fn) Y \<Longrightarrow> ti_ind (t2d ` (tf_set_struct t)) Y"
  by (subst (asm) ti_ind_fn) (simp only: ti_ind_ld')

lemma ti_ind_ld_list:
  "ti_ind (lf_set_list t fn) Y \<Longrightarrow> ti_ind (t2d ` (tf_set_list t)) Y"
  by (subst (asm) ti_ind_fn) (simp only: ti_ind_ld')

lemma ti_ind_ld_tuple:
  "ti_ind (lf_set_tuple t fn) Y \<Longrightarrow> ti_ind (t2d ` (tf_set_tuple t)) Y"
  by (subst (asm) ti_ind_fn) (simp only: ti_ind_ld')

lemma lf_set_fn':
  fixes t::"('a,'b) typ_info" and
    st::"('a,'b) typ_info_struct" and
    ts::"('a,'b) typ_info_tuple list" and
    x::"('a,'b) typ_info_tuple"
  shows
  "\<forall>s fn. s \<in> lf_set t fn \<longrightarrow> fn \<le> lf_fn s"
  "\<forall>s fn. s \<in> lf_set_struct st fn \<longrightarrow> fn \<le> lf_fn s"
  "\<forall>s fn. s \<in> lf_set_list ts fn \<longrightarrow> fn \<le> lf_fn s"
  "\<forall>s fn. s \<in> lf_set_tuple x fn \<longrightarrow> fn \<le> lf_fn s"
proof (induct t and st and ts and x)
  case (DTuple_typ_desc typ_desc list b)
  then show ?case 
    apply clarsimp
    subgoal for s fn
      apply(drule spec [where x=s])
      apply(drule spec [where x="fn @ [list]"])
      apply(clarsimp simp: prefix_def less_eq_list_def)
      done
    done
qed auto

lemma lf_set_fn:
  "s \<in> lf_set (t::('a,'b) typ_info) fn \<Longrightarrow> fn \<le> lf_fn s"
  by (clarsimp simp: lf_set_fn')

lemma ln_fn_disj:
  "dt_snd x \<notin> dt_snd ` set xs \<Longrightarrow> lf_fn ` lf_set_tuple x fn \<inter> lf_fn ` lf_set_list xs fn = {}"
  apply (induct xs arbitrary: x; clarsimp)
  apply (rule set_eqI, clarsimp)
  apply (erule disjE)
   apply (clarsimp dest!: lf_set_fn simp: split_DTuple_all prefix_def less_eq_list_def)
  apply fastforce
  done

lemma wf_lf_fn:
  fixes t::"('a,'b) typ_info" and
    st::"('a,'b) typ_info_struct" and
    ts::"('a,'b) typ_info_tuple list" and
    x::"('a,'b) typ_info_tuple"
  shows
  "\<forall>fn. wf_desc t \<longrightarrow> wf_lf (lf_set t fn) = wf_lf (lf_set t [])"
  "\<forall>fn. wf_desc_struct st \<longrightarrow> wf_lf (lf_set_struct st fn) = wf_lf (lf_set_struct  st [])"
  "\<forall>fn. wf_desc_list ts \<longrightarrow> wf_lf (lf_set_list ts fn) = wf_lf (lf_set_list ts [])"
  "\<forall>fn. wf_desc_tuple x \<longrightarrow> wf_lf (lf_set_tuple x fn) = wf_lf (lf_set_tuple x [])"
proof(induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case        
    apply clarify
    subgoal for fn
      apply(drule spec [where x=fn])
      apply clarsimp
      done
    done
next
  case (TypScalar nat1 nat2 a)
  then show ?case       
    apply clarsimp
    apply(clarsimp simp: wf_lf_def)
    done
next
  case (TypAggregate list)
  then show ?case 
    apply clarify
    subgoal for fn
     apply(drule spec [where x=fn])
    apply clarsimp
      done
    done
next
  case Nil_typ_desc
  then show ?case by clarsimp   
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case  
    apply clarify
    subgoal for fn
      apply(drule spec [where x=fn])+
      apply clarsimp
      apply(subst wf_lf_list)
       apply(erule ln_fn_disj)
      apply(subst wf_lf_list)
       apply(erule ln_fn_disj)
      apply clarsimp
      apply(subst ti_ind_fn)
      apply(subst ti_ind_sym2)
      apply(subst ti_ind_fn)
      apply(subst ti_ind_sym2)
      apply(clarsimp)
      done
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case 
    apply clarify
    subgoal for fn
      apply(frule spec [where x="[list]"])
      apply(drule spec [where x="fn@[list]"])
      apply clarsimp
      done
    done
qed

lemma wf_lf_fd_cons':
  fixes t::"('a,'b) typ_info" and
    st::"('a,'b) typ_info_struct" and
    ts::"('a,'b) typ_info_tuple list" and
    x::"('a,'b) typ_info_tuple"
  shows
  "\<forall>m. wf_lf (lf_set t []) \<longrightarrow> wf_desc t \<longrightarrow> fd_cons t"
  "\<forall>m. wf_lf (lf_set_struct st []) \<longrightarrow> wf_desc_struct st \<longrightarrow> fd_cons_struct st"
  "\<forall>m. wf_lf (lf_set_list ts []) \<longrightarrow> wf_desc_list ts \<longrightarrow> fd_cons_list ts"
  "\<forall>m. wf_lf (lf_set_tuple x []) \<longrightarrow> wf_desc_tuple x \<longrightarrow> fd_cons_tuple x"
proof(induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by clarsimp
next
  case (TypScalar nat1 nat2 a)
  then show ?case       
    apply(clarsimp simp: wf_lf_def fd_cons_struct_def fd_cons_def)
      apply(clarsimp simp: fd_cons_desc_def fd_cons_double_update_def fd_cons_update_access_def
                           fd_cons_access_update_def fd_cons_length_def)
    done
next
  case (TypAggregate list)
  then show ?case by clarsimp
next
  case Nil_typ_desc
  then show ?case by clarsimp
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case
   apply clarsimp
   apply(subst (asm) wf_lf_list)
    apply(erule ln_fn_disj)
   apply clarsimp
   apply(drule ti_ind_ld_td_tuple)
   apply(drule ti_ind_sym)
   apply(drule ti_ind_ld_td_list)
   apply(drule ti_ind_sym)
   apply(clarsimp simp: ti_ind_def)
   apply(clarsimp simp: fd_cons_list_def fd_cons_desc_def)
   apply(rule conjI)
    apply(clarsimp simp: fd_cons_tuple_def fd_cons_double_update_def fd_cons_desc_def)
    apply(simp add: fu_commutes_def)
   apply(rule conjI)
    apply(clarsimp simp: fd_cons_tuple_def fd_cons_update_access_def fd_cons_desc_def)
    apply(clarsimp simp: fd_cons_length_def)
   apply(rule conjI)
    apply(clarsimp simp: fd_cons_tuple_def fd_cons_desc_def)
     apply(clarsimp simp: fd_cons_access_update_def)
    subgoal for bs bs' v v'
    apply(simp add: fu_commutes_def)
      apply(clarsimp simp: fa_fu_ind_def)
      subgoal premises prems
        using prems (1-14, 16-18)
          prems (15)[rule_format, where bs'= "take (size_td_tuple dt_tuple) bs'" and 
            bs= "take (size_td_tuple dt_tuple) bs" and v="v" and v'="v'" ]
        apply -
        apply(simp add: min_ll)
        done
      done
    apply(clarsimp simp: fd_cons_length_def fd_cons_tuple_def fd_cons_desc_def)
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case   
    apply clarsimp
  apply(subst (asm) (2) wf_lf_fn, assumption)
  apply(clarsimp simp: fd_cons_def fd_cons_tuple_def export_uinfo_def)
  done
qed

lemma wf_lf_fd_cons:
  "\<lbrakk> wf_lf (lf_set t fn); wf_desc t \<rbrakk> \<Longrightarrow> fd_cons t"
  by (subst (asm) wf_lf_fn; simp only: wf_lf_fd_cons')

lemma wf_lf_fd_cons_struct:
  "\<lbrakk> wf_lf (lf_set_struct t fn); wf_desc_struct t \<rbrakk> \<Longrightarrow> fd_cons_struct t"
  by (subst (asm) wf_lf_fn; simp only: wf_lf_fd_cons')

lemma wf_lf_fd_cons_list:
  "\<lbrakk> wf_lf (lf_set_list t fn); wf_desc_list t \<rbrakk> \<Longrightarrow> fd_cons_list t"
  by (subst (asm) wf_lf_fn; simp only: wf_lf_fd_cons')

lemma wf_lf_fd_cons_tuple:
  "\<lbrakk> wf_lf (lf_set_tuple t fn); wf_desc_tuple t \<rbrakk> \<Longrightarrow> fd_cons_tuple t"
  by (subst (asm) wf_lf_fn; simp only: wf_lf_fd_cons')


lemma wf_lf_fdp':
  "\<forall>m. wf_lf (lf_set (t::('a,'b) typ_info) []) \<longrightarrow> wf_desc t \<longrightarrow> wf_fdp (tf_set t)"
  "\<forall>m. wf_lf (lf_set_struct (st::('a,'b) typ_info_struct) []) \<longrightarrow> wf_desc_struct st \<longrightarrow> wf_fdp (tf_set_struct st)"
  "\<forall>m. wf_lf (lf_set_list (ts::('a,'b) typ_info_tuple list) []) \<longrightarrow> wf_desc_list ts \<longrightarrow> wf_fdp (tf_set_list ts)"
  "\<forall>m. wf_lf (lf_set_tuple (x::('a,'b) typ_info_tuple) []) \<longrightarrow> wf_desc_tuple x \<longrightarrow> wf_fdp (tf_set_tuple x)"
proof (induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case 
    apply (clarsimp simp: wf_fdp_def)
    apply (fastforce elim: wf_lf_fd_cons_struct)
    done
next
  case (TypScalar nat1 nat2 a)
  then show ?case by (clarsimp simp: wf_fdp_def)
next
  case (TypAggregate list)
  then show ?case by (clarsimp simp: wf_fdp_def)
next
  case Nil_typ_desc
  then show ?case by (clarsimp simp: wf_fdp_def)
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case 
    apply (clarsimp simp: wf_fdp_def)
    apply(subst (asm) wf_lf_list)
     apply(erule ln_fn_disj)
    apply clarsimp
    apply(drule ti_ind_ld_tuple)
    apply(drule ti_ind_sym)
    apply(drule ti_ind_ld_list)
    apply(drule ti_ind_sym)
    apply(rule conjI, clarsimp)
     apply(erule disjE, fast)
     apply(clarsimp simp: ti_ind_def t2d_def)
    subgoal for x m y n
      apply(drule spec [where x="t2d (x,m)"])
      apply(drule spec [where x="t2d (y,n)"])
      apply(clarsimp simp: t2d_def image_def)
      apply(erule impE)
       apply(rule conjI)
        apply(rule bexI [where x="(x,m)"])
         apply clarsimp
        apply assumption
       apply(rule bexI [where x="(y,n)"])
        apply clarsimp
       apply assumption
      apply clarsimp
      done

    apply clarsimp
    subgoal for x m y n
      apply(erule disjE)
       apply(clarsimp simp: ti_ind_def t2d_def)
       apply(drule spec [where x="t2d (y,n)"])
       apply(drule spec [where x="t2d (x,m)"])
       apply(clarsimp simp: t2d_def image_def)
       apply(erule impE)
        apply(standard)
         apply(rule bexI [where x="(y,n)"])
          apply clarsimp
         apply assumption
        apply(rule bexI [where x="(x,m)"])
         apply clarsimp
        apply assumption
       apply clarsimp
       apply(clarsimp simp: fu_commutes_def)
      apply fast
      done
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case 
    apply (clarsimp simp: wf_fdp_def)
  apply(subst (asm) (2) wf_lf_fn, assumption)
  apply(clarsimp simp: wf_fdp_def)
    apply fast
    done
qed

lemma wf_lf_fdp:
  "\<lbrakk> wf_lf (lf_set t []); wf_desc t \<rbrakk> \<Longrightarrow> wf_fdp (tf_set t)"
  by (simp only: wf_lf_fdp')

lemma wf_fd_field_lookup [rule_format]:
  "\<forall>f m n s. wf_fd (t::('a,'b) typ_info) \<longrightarrow> field_lookup t f m = Some (s,n) \<longrightarrow> wf_fd s"
  "\<forall>f m n s. wf_fd_struct (st::('a,'b) typ_info_struct) \<longrightarrow> field_lookup_struct st f m = Some (s,n) \<longrightarrow> wf_fd s"
  "\<forall>f m n s. wf_fd_list (ts::('a,'b) typ_info_tuple list) \<longrightarrow> field_lookup_list ts f m = Some (s,n) \<longrightarrow> wf_fd s"
  "\<forall>f m n s. wf_fd_tuple (x::('a,'b) typ_info_tuple) \<longrightarrow> field_lookup_tuple x f m = Some (s,n) \<longrightarrow> wf_fd s"
  by (induct t and st and ts and x) (clarsimp split: option.splits)+

lemma wf_fd_field_lookupD:
  "\<lbrakk> field_lookup t f m = Some (s,n); wf_fd t \<rbrakk> \<Longrightarrow> wf_fd s"
  by (rule wf_fd_field_lookup)

lemma wf_fd_tf_set:
  "\<lbrakk> wf_fd t; ((s::('a,'b) typ_info),m) \<in> tf_set t \<rbrakk> \<Longrightarrow> wf_fd s"
  by (fastforce simp: tf_set_def wf_fd_field_lookupD)

lemma tf_set_field_lookupD:
  "field_lookup t f m = Some (s,n) \<Longrightarrow> (s,f) \<in> tf_set t"
  unfolding tf_set_def
  by (clarsimp simp flip: field_lookup_offset[where m=m] dest!: field_lookup_offset_le) arith

lemma fu_commutes_ts:
  "(\<And> t. t \<in> dt_fst ` set ts \<Longrightarrow> fu_commutes d (update_ti_t t)) \<Longrightarrow>
      fu_commutes d (update_ti_list_t ts)"
  by (induct ts; clarsimp simp: fu_commutes_def) (clarsimp simp: split_DTuple_all)

lemma fa_fu_ind_ts:
  "(\<And>t. t \<in> dt_fst ` set ts \<Longrightarrow> fa_fu_ind d (field_desc t) (size_td t) n) \<Longrightarrow>
      fa_fu_ind d \<lparr> field_access = access_ti_list ts,
              field_update = update_ti_list_t ts, field_sz = size_td_list ts\<rparr>
           (size_td_list ts) n"
  by (induct ts; clarsimp simp: fa_fu_ind_def) (clarsimp simp: split_DTuple_all)

lemma fa_fu_ind_ts2:
  "(\<And>t. t \<in> dt_fst ` set ts \<Longrightarrow> fa_fu_ind (field_desc t) d n (size_td t)) \<Longrightarrow>
      fa_fu_ind \<lparr> field_access = access_ti_list ts,
              field_update = update_ti_list_t ts, field_sz = size_td_list ts\<rparr> d
           n (size_td_list ts)"
  by (induct ts; clarsimp simp: fa_fu_ind_def) (clarsimp simp: split_DTuple_all)

lemma wf_fdp_fd [rule_format]:
  "\<forall>m. wf_fdp (tf_set t) \<longrightarrow> wf_desc t \<longrightarrow> wf_fd (t::('a,'b) typ_info)"
  "\<forall>m. (case st of TypScalar sz algn d \<Rightarrow> fd_cons_struct ((TypScalar sz algn d)::('a,'b) typ_info_struct)
           | _ \<Rightarrow> wf_fdp (tf_set_struct st)) \<longrightarrow> wf_desc_struct st \<longrightarrow> wf_fd_struct (st::('a,'b) typ_info_struct)"
  "\<forall>m. wf_fdp (tf_set_list ts) \<longrightarrow> wf_desc_list ts \<longrightarrow> wf_fd_list (ts::('a,'b) typ_info_tuple list)"
  "\<forall>m. wf_fdp (tf_set_tuple x) \<longrightarrow> wf_desc_tuple x \<longrightarrow> wf_fd_tuple (x::('a,'b) typ_info_tuple)"
proof(induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case  
    apply(clarsimp split: typ_struct.split_asm)
     apply(clarsimp simp: wf_fdp_def fd_cons_def fd_cons_struct_def)
    apply (fastforce dest: wf_fdp_mono)
    done
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
  case (Cons_typ_desc dt_tuple xs)
  then show ?case 
    apply clarsimp
    apply (rule conjI, fastforce dest: wf_fdp_mono)
    apply (rule conjI)
    subgoal
      using wf_fdp_mono
      by blast
    subgoal
      apply(clarsimp simp: wf_fdp_def)
      apply(cases dt_tuple, clarsimp)
      subgoal for a b x3

        apply(frule spec [where x=a])
        apply(drule spec [where x="[b]"])
        apply clarsimp
        apply (rule conjI)
         apply(rule fu_commutes_ts)
         apply clarsimp
        subgoal for x
          apply(drule spec [where x="dt_fst x"], erule impE, rule exI [where  x="[dt_snd x]"])
           apply (metis Prefix_Order.Cons_prefix_Cons dt_tuple.exhaust_sel rev_image_eqI tf_set_list_mem)
          apply simp
          done
        apply(rule conjI)
         apply(rule fa_fu_ind_ts)
         apply clarsimp
        subgoal for x

          apply(drule spec [where x="dt_fst x"], erule impE, rule exI [where x="[dt_snd x]"])
           apply (metis Prefix_Order.Cons_prefix_Cons dt_tuple.exhaust_sel rev_image_eqI tf_set_list_mem)
          apply simp
          done

        apply(rule fa_fu_ind_ts2)
        subgoal for t
          apply(drule spec [where x=t])
          apply clarsimp
          subgoal for x
            apply(cases x, clarsimp)
            subgoal for ba aa
              apply(drule spec [where x="[ba]"])
              apply clarsimp
              apply(simp add: tf_set_list_mem)
              apply clarsimp
              by (metis Prefix_Order.Cons_prefix_Cons dt_tuple.sel(2) imageI tf_set_self)

            done
          done
        done
      done
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case 
    apply(clarsimp simp: wf_fdp_def)
    subgoal for x m
      apply(drule spec [where x=x])
      apply(drule spec [where x="list#m"])
      apply clarsimp
      subgoal for y n
        apply(drule spec [where x=y])
        apply auto
        done
      done
    done
qed

lemma wf_fdp_fdD:
  "\<lbrakk> wf_fdp (tf_set t); wf_desc t \<rbrakk> \<Longrightarrow> wf_fd (t::('a,'b) typ_info)"
  by (rule wf_fdp_fd)

lemma wf_fdp_fd_listD:
  "\<lbrakk> wf_fdp (tf_set_list t); wf_desc_list t \<rbrakk> \<Longrightarrow> wf_fd_list t"
  by (rule wf_fdp_fd)

lemma fd_consistentD:
  "\<lbrakk> field_lookup t f 0 = Some (s,n); fd_consistent t \<rbrakk>
      \<Longrightarrow> fd_cons s"
  by (fastforce simp: fd_consistent_def)

lemma wf_fd_cons_access_update' [rule_format]:
  "wf_fd (t::('a,'b) typ_info) \<longrightarrow> fd_cons_access_update (field_desc t) (size_td t)"
  "wf_fd_struct (st::('a,'b) typ_info_struct) \<longrightarrow> fd_cons_access_update (field_desc_struct st) (size_td_struct st)"
  "wf_fd_list (ts::('a,'b) typ_info_tuple list) \<longrightarrow> fd_cons_access_update (field_desc_list ts) (size_td_list ts)"
  "wf_fd_tuple (x::('a,'b) typ_info_tuple) \<longrightarrow> fd_cons_access_update (field_desc_tuple x) (size_td_tuple x)"
proof(induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by (clarsimp split: typ_struct.splits)
next
  case (TypScalar nat1 nat2 a)
  then show ?case 
    apply (clarsimp split: typ_struct.splits)
    apply(clarsimp simp: fd_cons_access_update_def fd_cons_struct_def fd_cons_desc_def)
    done
next
  case (TypAggregate list)
  then show ?case by (clarsimp split: typ_struct.splits)
next
  case Nil_typ_desc
  then show ?case apply (clarsimp split: typ_struct.splits)
    apply(clarsimp simp: fd_cons_access_update_def)
    done
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case 
    apply (clarsimp split: typ_struct.splits)
    apply(clarsimp simp: fd_cons_access_update_def)
    apply(simp add: fu_commutes_def)
    apply(clarsimp simp: fa_fu_ind_def)
    by (metis (no_types, lifting) add_diff_cancel_left' length_drop length_take min_ll)
 next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case  by (clarsimp split: typ_struct.splits)
qed

lemma wf_fd_cons_access_updateD:
  "wf_fd t \<Longrightarrow> fd_cons_access_update (field_desc t) (size_td t)"
  by (rule wf_fd_cons_access_update')

lemma wf_fd_cons_access_update_structD:
  "wf_fd_struct t \<Longrightarrow> fd_cons_access_update (field_desc_struct t) (size_td_struct t)"
  by (rule wf_fd_cons_access_update')

lemma wf_fd_cons_access_update_listD:
  "wf_fd_list t \<Longrightarrow> fd_cons_access_update (field_desc_list t) (size_td_list t)"
  by (rule wf_fd_cons_access_update')

lemma wf_fd_cons_access_update_tupleD:
  "wf_fd_tuple t \<Longrightarrow> fd_cons_access_update (field_desc_tuple t) (size_td_tuple t)"
  by (rule wf_fd_cons_access_update')

lemma wf_fd_norm_tu:
  "\<forall>bs. wf_fd t \<longrightarrow> length bs = size_td t \<longrightarrow> norm_tu (export_uinfo (t::('a,'b) typ_info)) bs = (access_ti t (update_ti_t t bs undefined) (replicate (size_td t) 0))"
  "\<forall>bs. wf_fd_struct st \<longrightarrow> length bs = size_td_struct st \<longrightarrow> norm_tu_struct (map_td_struct field_norm (\<lambda>_. ()) (st::('a,'b) typ_info_struct)) bs = (access_ti_struct st (update_ti_struct_t st bs undefined) (replicate (size_td_struct st) 0))"
  "\<forall>bs. wf_fd_list ts \<longrightarrow> length bs = size_td_list ts \<longrightarrow> norm_tu_list (map_td_list field_norm (\<lambda>_. ()) (ts::('a,'b) typ_info_tuple list)) bs = (access_ti_list ts (update_ti_list_t ts bs undefined) (replicate (size_td_list ts) 0))"
  "\<forall>bs. wf_fd_tuple x \<longrightarrow> length bs = size_td_tuple x \<longrightarrow> norm_tu_tuple (map_td_tuple field_norm (\<lambda>_. ()) (x::('a,'b) typ_info_tuple)) bs = (access_ti_tuple x (update_ti_tuple_t x bs undefined) (replicate (size_td_tuple x) 0))"
  apply(induct t and st and ts and x, all \<open>clarsimp simp: export_uinfo_def\<close>)
   apply(simp add: field_norm_def)
  apply(simp add: fu_commutes_def)
  apply(simp add: fa_fu_ind_def)
  apply(drule wf_fd_cons_access_update_listD)
  apply(clarsimp simp: fd_cons_access_update_def export_uinfo_def min_def)
  done

lemma wf_fd_norm_tuD:
  "\<lbrakk> wf_fd t; length bs = size_td t \<rbrakk>  \<Longrightarrow> norm_tu (export_uinfo t) bs =
      (access_ti\<^sub>0 t (update_ti_t t bs undefined))"
  using wf_fd_norm_tu(1) [of t] by (clarsimp simp: access_ti\<^sub>0_def)

lemma wf_fd_norm_tu_structD:
  "\<lbrakk> wf_fd_struct t; length bs = size_td_struct t \<rbrakk> \<Longrightarrow> norm_tu_struct (map_td_struct field_norm (\<lambda>_. ()) t) bs =
      (access_ti_struct t (update_ti_struct_t t bs undefined) (replicate (size_td_struct t) 0))"
  using wf_fd_norm_tu(2) [of t] by clarsimp

lemma wf_fd_norm_tu_listD:
  "\<lbrakk> wf_fd_list t; length bs = size_td_list t \<rbrakk> \<Longrightarrow> norm_tu_list (map_td_list field_norm (\<lambda>_. ()) t) bs =
      (access_ti_list t (update_ti_list_t t bs undefined) (replicate (size_td_list t) 0))"
  using wf_fd_norm_tu(3) [of t] by clarsimp

lemma wf_fd_norm_tu_tupleD:
  "\<lbrakk> wf_fd_tuple t; length bs = size_td_tuple t \<rbrakk> \<Longrightarrow> norm_tu_tuple (map_td_tuple field_norm (\<lambda>_. ()) t) bs =
      (access_ti_tuple t (update_ti_tuple_t t bs undefined) (replicate (size_td_tuple t) 0))"
  using wf_fd_norm_tu(4) [of t] by clarsimp

lemma wf_fd_cons [rule_format]:
  "wf_fd t \<longrightarrow> fd_cons (t::('a,'b) typ_info)"
  "wf_fd_struct st \<longrightarrow> fd_cons_struct (st::('a,'b) typ_info_struct)"
  "wf_fd_list ts \<longrightarrow> fd_cons_list (ts::('a,'b) typ_info_tuple list)"
  "wf_fd_tuple x \<longrightarrow> fd_cons_tuple (x::('a,'b) typ_info_tuple)"
proof (induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by auto
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
  then show ?case 
    apply clarsimp
    apply(clarsimp simp: fd_cons_list_def fd_cons_desc_def)
    apply (rule conjI)
     apply(clarsimp simp: fd_cons_tuple_def fd_cons_double_update_def fd_cons_desc_def)
     apply(simp add: fu_commutes_def)
    apply (rule conjI)
     apply(clarsimp simp: fd_cons_tuple_def fd_cons_update_access_def fd_cons_desc_def)
     apply(clarsimp simp: fd_cons_length_def)
    apply (rule conjI)
     apply(clarsimp simp: fd_cons_tuple_def fd_cons_desc_def)
     apply(clarsimp simp: fd_cons_access_update_def fu_commutes_def fa_fu_ind_def )
     apply (smt (verit) diff_add_inverse length_drop length_take min_ll)
    apply(clarsimp simp: fd_cons_length_def fd_cons_tuple_def  fd_cons_desc_def)
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by(clarsimp simp: fd_cons_def fd_cons_tuple_def export_uinfo_def)
qed

lemma wf_fd_consD:
  "wf_fd t \<Longrightarrow> fd_cons t"
  by (rule wf_fd_cons)

lemma wf_fd_cons_structD:
  "wf_fd_struct t \<Longrightarrow> fd_cons_struct t"
  by (rule wf_fd_cons)

lemma wf_fd_cons_listD:
  "wf_fd_list t \<Longrightarrow> fd_cons_list t"
  by (rule wf_fd_cons)

lemma wf_fd_cons_tupleD:
  "wf_fd_tuple t \<Longrightarrow> fd_cons_tuple t"
  by (rule wf_fd_cons)

lemma fd_cons_list_append:
  "\<lbrakk> wf_fd_list xs; wf_fd_list ys; fu_commutes
      (field_update (field_desc_list xs)) (field_update (field_desc_list ys)) \<rbrakk> \<Longrightarrow>
      fd_cons_list (xs@ys)"
  apply(frule wf_fd_cons_listD)
  apply(frule wf_fd_cons_listD [where t=ys])
  apply(unfold fd_cons_list_def fd_cons_desc_def)
  apply(fastforce intro: fd_cons_double_update_list_append fd_cons_update_access_list_append
                         fd_cons_access_update_list_append fd_cons_length_list_append)
  done


lemma (in wf_type) wf_fd  [simp]:
  "wf_fd (typ_info_t TYPE('a))"
  by (fastforce intro: wf_fdp_fdD wf_lf_fdp wf_lf)

lemma (in wf_type) fd_cons [simp]:
  "fd_consistent (typ_info_t TYPE('a))"
  unfolding fd_consistent_def by (fastforce intro: wf_fd_consD wf_fd_field_lookupD)


lemma (in wf_type) field_lvalue_append [simp]:
  "\<lbrakk> field_ti TYPE('a) f = Some t;
      export_uinfo t = typ_uinfo_t TYPE('b::c_type);
      field_ti TYPE('b) g = Some k \<rbrakk> \<Longrightarrow>
          &(((Ptr &((p::'a ptr)\<rightarrow>f))::'b ptr)\<rightarrow>g) = &(p\<rightarrow>f@g)"
  apply(clarsimp simp: field_lvalue_def c_type_class.field_ti_def field_ti_def field_offset_def
                       field_offset_untyped_def typ_uinfo_t_def
                 split: option.splits)
  apply(subst field_lookup_prefix_Some')
    apply(fastforce dest: field_lookup_export_uinfo_Some)
   apply(simp add: export_uinfo_def wf_desc_map)
  apply(drule field_lookup_export_uinfo_Some)
  apply(simp add: export_uinfo_def)
  apply(drule field_lookup_export_uinfo_Some)
  apply(simp add: export_uinfo_def)
  apply (simp add: c_type_class.field_lvalue_def c_type_class.field_offset_def 
        c_type_class.typ_uinfo_t_def export_uinfo_def field_lookup_offset_shift' field_offset_untyped_def)
  done



lemma (in wf_type) field_lvalue_cons_unfold':
\<comment> \<open>rhs contains additional type variable @{typ 'b}, hence simplifier won't apply this rule\<close>
  "\<lbrakk> field_ti TYPE('a) [f] = Some t;
      export_uinfo t = typ_uinfo_t TYPE('b::c_type);
      field_ti TYPE('b) g = Some k \<rbrakk> \<Longrightarrow>
          &(p\<rightarrow>f#g) = &(((Ptr &((p::'a ptr)\<rightarrow>[f]))::'b ptr)\<rightarrow>g)"
  using field_lvalue_append [where f="[f]" and g=g]
  by simp

lemma (in mem_type) field_lvalue_cons_unfold:
  "\<lbrakk>field_ti TYPE('b) g = Some k;
    export_uinfo t = export_uinfo (typ_info_t TYPE('b::c_type));
    field_ti TYPE('a) [f] = Some t\<rbrakk> \<Longrightarrow>
      &(p\<rightarrow>f#g) \<equiv> &(((Ptr &((p::'a ptr)\<rightarrow>[f]))::'b ptr)\<rightarrow>g)"
  using field_lvalue_cons_unfold' [simplified c_type_class.typ_uinfo_t_def]
  apply -
  apply (rule eq_reflection)
  apply blast
  done

lemma field_access_update_take_drop [rule_format]:
  "\<forall>f s m n bs bs' v. field_lookup t f m = Some (s,m+n) \<longrightarrow>
      length bs = size_td t \<longrightarrow> length bs' = size_td s \<longrightarrow> wf_fd t \<longrightarrow>
      field_access (field_desc s) (field_update (field_desc t) bs v) bs'
          = field_access (field_desc s) (field_update (field_desc s)
              (take (size_td (s::('a,'b) typ_info)) (drop n bs)) undefined) bs'"
  "\<forall>f s m n bs bs' v. field_lookup_struct st f m = Some (s,m+n) \<longrightarrow>
      length bs = size_td_struct st \<longrightarrow> length bs' = size_td s \<longrightarrow> wf_fd_struct st \<longrightarrow>
      field_access (field_desc s) (field_update (field_desc_struct st) bs v) bs'
          = field_access (field_desc s) (field_update (field_desc s)
              (take (size_td (s::('a,'b) typ_info)) (drop n bs)) undefined) bs'"
  "\<forall>f s m n bs bs' v. field_lookup_list ts f m = Some (s,m+n) \<longrightarrow>
      length bs = size_td_list ts \<longrightarrow> length bs' = size_td s \<longrightarrow> wf_fd_list ts \<longrightarrow>
      field_access (field_desc s) (field_update (field_desc_list ts) bs v) bs'
          = field_access (field_desc s) (field_update (field_desc s)
              (take (size_td (s::('a,'b) typ_info)) (drop n bs)) undefined) bs'"
  "\<forall>f s m n bs bs' v. field_lookup_tuple x f m = Some (s,m+n) \<longrightarrow>
      length bs = size_td_tuple x \<longrightarrow> length bs' = size_td s \<longrightarrow> wf_fd_tuple x \<longrightarrow>
      field_access (field_desc s) (field_update (field_desc_tuple x) bs v) bs'
          = field_access (field_desc s) (field_update (field_desc s)
              (take (size_td (s::('a,'b) typ_info)) (drop n bs)) undefined) bs'"
proof (induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case 
    apply clarsimp   
    apply(fastforce dest!: wf_fd_cons_structD
        simp: fd_cons_struct_def fd_cons_desc_def fd_cons_access_update_def)
    done
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
  then show ?case 
    apply clarsimp
    subgoal for f s m n bs bs' v
      apply(clarsimp simp: fd_cons_desc_def split: option.splits)
       apply(cases f; clarsimp)
      subgoal premises prems for a lista
        using prems (1-7, 10-12)
          prems(9) [rule_format, where f= "a#lista" and s=s and m= "m + size_td (dt_fst dt_tuple)" and n="n - size_td (dt_fst dt_tuple)"] 
        apply clarsimp
        apply(frule field_lookup_offset_le)
        apply simp
        apply(cases dt_tuple, clarsimp simp: fu_commutes_def)
        done
      apply(cases f; clarsimp)
      subgoal for a lista
        apply(drule spec [where x="a#lista"])
        apply(drule spec [where x="s"])
        apply(drule spec [where x="m"])
        apply(drule spec [where x="n"])
        apply clarsimp
        apply(frule field_lookup_offset_le)
        apply simp
        apply(cases dt_tuple, clarsimp)
        apply(clarsimp split: if_split_asm)
        by(fastforce dest: td_set_field_lookupD td_set_offset_size_m simp: ac_simps drop_take min_def)
      done
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by auto
qed


lemma field_access_update_take_dropD:
  "\<lbrakk> field_lookup t f m = Some (s,m+n); length bs = size_td t;
      length bs' = size_td s; wf_fd t \<rbrakk> \<Longrightarrow>
      field_access (field_desc s) (field_update (field_desc t) bs v) bs'
          = field_access (field_desc s) (field_update (field_desc s)
              (take (size_td (s::('a,'b) typ_info)) (drop n bs)) undefined) bs'"
  by (rule field_access_update_take_drop)

lemma (in wf_type) fi_fa_consistentD:
  "\<lbrakk> field_lookup (typ_info_t TYPE('a)) f 0 = Some (d,n);
      length bs = size_of TYPE('a) \<rbrakk> \<Longrightarrow>
      field_access (field_desc d) (from_bytes bs) (replicate (size_td d) 0) =
      norm_tu (export_uinfo d) (take (size_td d) (drop n bs))"
  apply(clarsimp simp: field_offset_def from_bytes_def size_of_def)
  apply(frule field_lookup_export_uinfo_Some)
  apply(subst wf_fd_norm_tuD)
    apply(fastforce intro: wf_fd_field_lookupD)
   apply(clarsimp simp: min_def split: if_split_asm)
   apply(drule td_set_field_lookupD)
   apply(drule td_set_offset_size)
   apply simp
  apply(frule field_access_update_take_dropD[where v=undefined and m=0 and
                                                   bs'="replicate (size_td d) 0",simplified]; simp?)
  apply(simp add: min_def access_ti\<^sub>0_def)
  done

lemma fi_fu_consistent [rule_format]:
  "\<forall>f m n s bs v w. field_lookup t f m = Some (s,n + m) \<longrightarrow> wf_fd t \<longrightarrow>
      length bs = size_td t \<longrightarrow> length v = size_td (s::('a,'b) typ_info) \<longrightarrow>
      field_update (field_desc t) (super_update_bs v bs n) w =
          field_update (field_desc s) v (field_update (field_desc t) bs w)"
  "\<forall>f m n s bs v w. field_lookup_struct st f m = Some (s,n + m) \<longrightarrow> wf_fd_struct st \<longrightarrow>
      length bs = size_td_struct  st \<longrightarrow> length v = size_td (s::('a,'b) typ_info) \<longrightarrow>
      field_update (field_desc_struct st) (super_update_bs v bs n) w =
          field_update (field_desc s) v (field_update (field_desc_struct  st) bs w)"
  "\<forall>f m n s bs v w. field_lookup_list ts f m = Some (s,n + m) \<longrightarrow> wf_fd_list ts \<longrightarrow>
      length bs = size_td_list ts \<longrightarrow> length v = size_td (s::('a,'b) typ_info) \<longrightarrow>
      field_update (field_desc_list ts) (super_update_bs v bs n) w =
          field_update (field_desc s) v (field_update (field_desc_list ts) bs w)"
  "\<forall>f m n s bs v w. field_lookup_tuple x f m = Some (s,n + m) \<longrightarrow> wf_fd_tuple x \<longrightarrow>
      length bs = size_td_tuple x \<longrightarrow> length v = size_td (s::('a,'b) typ_info) \<longrightarrow>
      field_update (field_desc_tuple x) (super_update_bs v bs n) w =
          field_update (field_desc s) v (field_update (field_desc_tuple x) bs w)"
proof(induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case 
    apply clarsimp
    apply(drule wf_fd_cons_structD)
    apply(clarsimp simp: fd_cons_struct_def fd_cons_double_update_def super_update_bs_def
        fd_cons_desc_def)
    done
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
  then show ?case 
    apply clarsimp
    subgoal for f m n s bs v w
      apply(cases f; clarsimp)
      apply(clarsimp simp: fd_cons_desc_def split: option.splits)
       apply(clarsimp simp: fu_commutes_def)
      subgoal premises prems for a lista
        using prems (1-8,11-12)
          prems(10)[rule_format, where f="a#lista" and s= s and m="m + size_td (dt_fst dt_tuple)" 
            and n= "n - size_td (dt_fst dt_tuple)"] 
        apply -
        apply(frule field_lookup_offset_le)
        apply simp
        apply(drule td_set_list_field_lookup_listD)
        apply(drule td_set_list_offset_size_m)
        apply (cases dt_tuple)
        apply(clarsimp simp: drop_super_update_bs take_super_update_bs)
        done
      subgoal for a lista
        apply(simp add: fu_commutes_def)
        by (smt (verit, best) add.commute append_take_drop_id diff_add_inverse2 
            length_append length_super_update_bs length_take min_ll 
            super_update_bs_append_drop_first super_update_bs_append_take_first 
            td_set_offset_size' td_set_tuple_field_lookup_tupleD)
      done
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by auto
qed


lemma fi_fu_consistentD:
  "\<lbrakk> field_lookup t f 0 = Some (s,n); wf_fd t; length bs = size_td t;
      length v = size_td s \<rbrakk> \<Longrightarrow>
      field_update (field_desc t) (super_update_bs v bs n) w =
          field_update (field_desc s) v (field_update (field_desc t) bs w)"
  using fi_fu_consistent(1) [of t f 0] by clarsimp

lemma (in wf_type) norm:
  assumes lbs: "length bs = size_of TYPE('a)" 
  shows "from_bytes (norm_bytes TYPE('a) bs) = ((from_bytes bs)::'a)"
proof -
  have "wf_fd (typ_info_t TYPE('a))"
    by simp
  with lbs  show ?thesis 
    apply -
    apply(drule wf_fd_consD)
    apply(simp add: from_bytes_def norm_bytes_def)
    apply(clarsimp simp: fd_cons_def fd_cons_desc_def)
    apply(drule (3) fd_cons_update_normalise)
    apply(fastforce simp: fd_cons_update_normalise_def size_of_def wf_fd_norm_tuD norm_desc_def
        access_ti\<^sub>0_def)
    done
qed

lemma (in wf_type) len:
  "length bs = size_of TYPE('a) \<Longrightarrow>
      length (to_bytes (x::'a) bs) = size_of TYPE('a)"
  apply(simp add: size_of_def to_bytes_def)
  by (metis fd_cons_def fd_cons_desc_def fd_cons_length_def 
      field_desc.simps(1) field_desc_def local.wf_fd wf_fd_consD)


lemma (in wf_type) sz_nzero:
  "0 < size_of (TYPE('a))"
  unfolding size_of_def
  by (simp add: wf_size_desc_gt)

lemma not_disj_fn_empty1 [simp]:
  "\<not> disj_fn [] s"
  by (simp add: disj_fn_def)

lemma disj_fn_comm: "disj_fn a b \<longleftrightarrow> disj_fn b a"
  by (auto simp add: disj_fn_def)

lemma disj_fn_append_right: "disj_fn x y \<Longrightarrow> disj_fn x (y @ z)"
  by (auto simp: disj_fn_def less_eq_list_def prefix_def append_eq_append_conv2)

lemma disj_fn_cons_consI[simp]: "(x = y \<longrightarrow> disj_fn a b) \<Longrightarrow> disj_fn (x # a) (y # b)"
  by (auto simp: disj_fn_def)

lemma fd_path_cons [simp]:
  "f \<notin> fs_path (x#xs) = (disj_fn f x \<and> f \<notin> fs_path xs)"
  by (auto simp: fs_path_def disj_fn_def)

lemma fu_commutes_lookup_disjD:
  "\<lbrakk> field_lookup t f m = Some (d,n); field_lookup t f' m' = Some (d',n');
      disj_fn f f'; wf_fdp (tf_set t) \<rbrakk> \<Longrightarrow>
      fu_commutes (field_update (field_desc (d::('a,'b) typ_info)))
          (field_update (field_desc d'))"
  by (auto simp: disj_fn_def wf_fdp_def dest!: tf_set_field_lookupD)

lemma field_lookup_fa_fu_lhs:
  "\<forall>f m n s d k. field_lookup t f m = Some (s,n) \<longrightarrow> fa_fu_ind (field_desc t) d k (size_td t)
      \<longrightarrow> wf_fd t \<longrightarrow> fa_fu_ind (field_desc (s::('a,'b) typ_info)) d k (size_td s)"
  "\<forall>f m n s d k. field_lookup_struct st f m = Some (s,n) \<longrightarrow> fa_fu_ind (field_desc_struct st) d k (size_td_struct st)
      \<longrightarrow> wf_fd_struct st \<longrightarrow> fa_fu_ind (field_desc (s::('a,'b) typ_info)) d k (size_td s)"
  "\<forall>f m n s d k. field_lookup_list ts f m = Some (s,n) \<longrightarrow> fa_fu_ind (field_desc_list ts) d k (size_td_list ts)
      \<longrightarrow> wf_fd_list ts \<longrightarrow> fa_fu_ind (field_desc (s::('a,'b) typ_info)) d k (size_td s)"
  "\<forall>f m n s d k. field_lookup_tuple x f m = Some (s,n) \<longrightarrow> fa_fu_ind (field_desc_tuple x) d k (size_td_tuple x)
      \<longrightarrow> wf_fd_tuple x \<longrightarrow> fa_fu_ind (field_desc (s::('a,'b) typ_info)) d k (size_td s)"
proof (induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by (clarsimp simp: fa_fu_ind_def)
next
  case (TypScalar nat1 nat2 a)
  then show ?case by (clarsimp simp: fa_fu_ind_def)
next
  case (TypAggregate list)
  then show ?case by (clarsimp simp: fa_fu_ind_def)
next
  case Nil_typ_desc
  then show ?case by (clarsimp simp: fa_fu_ind_def)
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case 
    apply (clarsimp simp: fa_fu_ind_def)
    subgoal for  f m n s d v bs bs'
      apply(clarsimp split: option.splits)
      subgoal premises prems 
        using prems (1-8, 10) 
        apply -
        apply (rule 
            prems (9)[rule_format, where f=f and s = s and m = "m + size_td (dt_fst dt_tuple)"
              and n=n and d=d and k="length bs", OF prems(11), simplified])
        subgoal for v ys ys'
          apply(drule spec [where x=v])
          apply(drule spec [where x=ys])
          apply clarsimp
          apply(drule spec [where x="replicate (size_td_tuple dt_tuple) 0 @ ys'"])
          apply clarsimp
          apply(drule wf_fd_cons_tupleD)
          apply(clarsimp simp: fd_cons_tuple_def fd_cons_length_def fd_cons_desc_def)
          done
        subgoal by clarsimp
        subgoal by fast
        done
      subgoal
        apply(drule spec [where x=f])
        apply(drule spec [where x=m])
        apply(drule spec [where x=n])
        apply(drule spec [where x=s])
        apply clarsimp
        apply(drule spec [where x=d])
        apply(drule spec [where x="length bs"])
        apply(erule impE)
         apply clarsimp
        subgoal for  v ys ys'
          apply(drule spec [where x=v])
          apply(drule spec [where x=ys])
          apply clarsimp
          apply(drule spec [where x="ys'@replicate (size_td_list list) 0"])
          apply clarsimp
          apply(drule wf_fd_cons_tupleD)
          apply(clarsimp simp: fd_cons_tuple_def fd_cons_length_def fd_cons_desc_def)
          done
        apply clarsimp
        done
      done
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by (clarsimp simp: fa_fu_ind_def)
qed

lemma field_lookup_fa_fu_lhs_listD:
  "\<lbrakk> field_lookup_list ts f m = Some (s,n); fa_fu_ind (field_desc_list ts) d k (size_td_list ts);
      wf_fd_list ts \<rbrakk> \<Longrightarrow> fa_fu_ind (field_desc (s::('a,'b) typ_info)) d k (size_td s) "
  using field_lookup_fa_fu_lhs(3) [of ts] by blast

lemma field_lookup_fa_fu_lhs_tupleD:
  "\<lbrakk> field_lookup_tuple x f m = Some (s,n); fa_fu_ind (field_desc_tuple x) d k (size_td_tuple x);
      wf_fd_tuple x \<rbrakk> \<Longrightarrow> fa_fu_ind (field_desc (s::('a,'b) typ_info)) d k (size_td s)"
  using field_lookup_fa_fu_lhs(4) [of x] by blast

lemma field_lookup_fa_fu_rhs:
  "\<forall>f m n s d k . field_lookup t f m = Some (s,n) \<longrightarrow> fa_fu_ind d (field_desc t) (size_td t) k
      \<longrightarrow> wf_fd t \<longrightarrow> fa_fu_ind d (field_desc (s::('a,'b) typ_info)) (size_td s) k"
  "\<forall>f m n s d k. field_lookup_struct st f m = Some (s,n) \<longrightarrow> fa_fu_ind d (field_desc_struct st) (size_td_struct st) k
      \<longrightarrow> wf_fd_struct st \<longrightarrow> fa_fu_ind d (field_desc (s::('a,'b) typ_info)) (size_td s) k"
  "\<forall>f m n s d k. field_lookup_list ts f m = Some (s,n) \<longrightarrow> fa_fu_ind d (field_desc_list ts) (size_td_list ts) k
      \<longrightarrow> wf_fd_list ts \<longrightarrow> fa_fu_ind d (field_desc (s::('a,'b) typ_info)) (size_td s) k"
  "\<forall>f m n s d k. field_lookup_tuple x f m = Some (s,n) \<longrightarrow> fa_fu_ind d (field_desc_tuple x) (size_td_tuple x) k
      \<longrightarrow> wf_fd_tuple x \<longrightarrow> fa_fu_ind d (field_desc (s::('a,'b) typ_info)) (size_td s) k"
proof (induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by (clarsimp simp: fa_fu_ind_def)
next
  case (TypScalar nat1 nat2 a)
  then show ?case by (clarsimp simp: fa_fu_ind_def)
next
  case (TypAggregate list)
  then show ?case by (clarsimp simp: fa_fu_ind_def)
next
  case Nil_typ_desc
  then show ?case by (clarsimp simp: fa_fu_ind_def)
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case 
    apply (clarsimp simp: fa_fu_ind_def)
    subgoal for f m n s d v bs bs'
      apply(clarsimp split: option.splits)
      subgoal premises prems 
        thm prems
        using prems (1-8, 10) 
        apply -
        apply (rule 
            prems (9)[rule_format, where f=f and s = s and m = "m + size_td (dt_fst dt_tuple)"
              and n=n and d=d and k="length bs'", OF prems(11), simplified])
        subgoal for v ys ys'
          apply(drule spec [where x=v])
          apply(drule spec [where x="access_ti_tuple dt_tuple v (replicate (size_td_tuple dt_tuple) 0)@ys"])
          apply clarsimp

          apply(drule wf_fd_cons_tupleD)
          apply(clarsimp simp: fd_cons_tuple_def fd_cons_length_def fd_cons_desc_def)
          apply(drule spec [where x="ys'"])
          apply(clarsimp simp: fd_cons_tuple_def fd_cons_length_def fd_cons_update_access_def fd_cons_desc_def)
          apply(clarsimp simp: fu_commutes_def)
          done
        subgoal by clarsimp
        subgoal
          apply(drule spec [where x=f])
          apply(drule spec [where x=m])
          apply(drule spec [where x=n])
          apply(drule spec [where x=s])
          apply clarsimp
          done
        done
      subgoal
        apply(drule spec [where x=f])
        apply(drule spec [where x=m])
        apply(drule spec [where x=n])
        apply(drule spec [where x=s])
        apply clarsimp
        apply(drule spec [where x=d])
        apply(drule spec [where x="length bs'"])
        apply(erule impE)
         apply clarsimp
        subgoal for v ys ys'
          apply(drule spec [where x=v])
          apply(drule spec [where x="ys@access_ti_list list v (replicate (size_td_list list) 0)"])
          apply(drule wf_fd_cons_tupleD)
          apply(drule wf_fd_cons_listD)
          apply(clarsimp simp: fd_cons_tuple_def fd_cons_list_def fd_cons_length_def
              fd_cons_update_access_def fd_cons_desc_def)
          done
        apply fastforce
        done
      done
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case by (clarsimp simp: fa_fu_ind_def)
qed

lemma field_lookup_fa_fu_rhs_listD:
  "\<lbrakk> field_lookup_list ts f m = Some (s,n);
      fa_fu_ind d (field_desc_list ts) (size_td_list ts) k; wf_fd_list ts \<rbrakk> \<Longrightarrow>
      fa_fu_ind d (field_desc (s::('a,'b) typ_info)) (size_td s) k"
  using field_lookup_fa_fu_rhs(3) [of ts] by blast

lemma field_lookup_fa_fu_rhs_tupleD:
  "\<lbrakk> field_lookup_tuple x f m = Some (s,n);
      fa_fu_ind d (field_desc_tuple x) (size_td_tuple x) k; wf_fd_tuple x \<rbrakk> \<Longrightarrow>
      fa_fu_ind d (field_desc (s::('a,'b) typ_info)) (size_td s) k"
  using field_lookup_fa_fu_rhs(4) [of x] by blast


lemma fa_fu_lookup_ind_list_tuple:
  shows
  "\<lbrakk> field_lookup_tuple x f m = Some (d',n); wf_fd_tuple x;
      field_lookup_list ts f' m' = Some (d,n'); wf_fd_list ts;
      fa_fu_ind (field_desc_list ts) (field_desc_tuple x) (size_td_tuple x) (size_td_list ts) \<rbrakk>
      \<Longrightarrow> fa_fu_ind (field_desc d) (field_desc d') (size_td d') (size_td d)"
  apply(drule (2) field_lookup_fa_fu_lhs_listD)
  apply(drule (3) field_lookup_fa_fu_rhs_tupleD)
  done

lemma fa_fu_lookup_ind_tuple_list:
  "\<lbrakk> field_lookup_tuple x f m = Some (d,n); wf_fd_tuple x;
      field_lookup_list ts f' m' = Some (d',n'); wf_fd_list ts;
      fa_fu_ind (field_desc_tuple x) (field_desc_list ts) (size_td_list ts) (size_td_tuple x) \<rbrakk>
      \<Longrightarrow> fa_fu_ind (field_desc d) (field_desc d') (size_td d') (size_td d)"
  apply(drule (2) field_lookup_fa_fu_lhs_tupleD)
  apply(drule (3) field_lookup_fa_fu_rhs_listD)
  done

lemma fa_fu_lookup_disj:
  "\<forall>f m d n f' m' d' n'. field_lookup t f m = Some (d,n) \<longrightarrow>
      field_lookup t f' m' = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd t \<longrightarrow> fa_fu_ind (field_desc (d::('a,'b) typ_info)) (field_desc d') (size_td d') (size_td d)"
  "\<forall>f m d n f' m' d' n'. field_lookup_struct st f m = Some (d,n) \<longrightarrow>
      field_lookup_struct st f' m' = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd_struct st \<longrightarrow> fa_fu_ind (field_desc (d::('a,'b) typ_info)) (field_desc d') (size_td d') (size_td d)"
  "\<forall>f m d n f' m' d' n'. field_lookup_list ts f m = Some (d,n) \<longrightarrow>
      field_lookup_list ts f' m' = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd_list ts \<longrightarrow> fa_fu_ind (field_desc (d::('a,'b) typ_info)) (field_desc d') (size_td d') (size_td d)"
  "\<forall>f m d n f' m' d' n'. field_lookup_tuple x f m = Some (d,n) \<longrightarrow>
      field_lookup_tuple x f' m' = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd_tuple x \<longrightarrow> fa_fu_ind (field_desc (d::('a,'b) typ_info)) (field_desc d') (size_td d') (size_td d)"
proof (induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by (clarsimp simp: disj_fn_def)
next
  case (TypScalar nat1 nat2 a)
  then show ?case by (clarsimp simp: disj_fn_def)
next
  case (TypAggregate list)
  then show ?case by (clarsimp simp: disj_fn_def)
next
  case Nil_typ_desc
  then show ?case by (clarsimp simp: disj_fn_def)
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case 
    apply (clarsimp simp: disj_fn_def)
    apply(clarsimp simp: split: option.splits)
    subgoal by blast
    subgoal 
      by(drule (3) fa_fu_lookup_ind_list_tuple; simp)
    subgoal by (drule (3) fa_fu_lookup_ind_tuple_list; simp)
    subgoal for f m d n f' m' d' n'
      apply(drule spec [where x=f ])
      apply(drule spec [where x=m])
      apply(drule spec [where x=d])
      apply clarsimp
      by blast
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case 
    apply(clarsimp simp: disj_fn_def)
    subgoal for f m d n f' m' d' n'
      apply(drule spec [where x="tl f"])
      apply(drule spec [where x=m])
      apply(drule spec [where x=d])
      apply clarsimp
      apply(drule spec [where x="tl f'"])
      apply(drule spec [where x=m'])
      apply(drule spec [where x=d'])
      apply clarsimp
      apply(cases f; clarsimp)
      apply(cases f'; clarsimp)
      done
    done
qed

lemma fa_fu_lookup_disjD:
  "\<lbrakk> field_lookup t f m = Some (d,n); field_lookup t f' m' = Some (d',n');
      disj_fn f f'; wf_fd t \<rbrakk> \<Longrightarrow>
      fa_fu_ind (field_desc (d::('a,'b) typ_info)) (field_desc d') (size_td d') (size_td d)"
 using fa_fu_lookup_disj(1) [of t] by fastforce

lemma field_access_update_disj:
  "\<lbrakk> field_lookup t f m = Some (d,n); field_lookup t f' m' = Some (d',n');
      disj_fn f f'; length bs = size_td d'; length bs' = size_td d; wf_fd t \<rbrakk> \<Longrightarrow>
      access_ti d (update_ti_t d' bs v) bs' = access_ti d v bs'"
  by (fastforce dest: fa_fu_lookup_disjD simp: fa_fu_ind_def)

lemma td_set_list_intvl_sub:
  "(d,n) \<in> td_set_list t m \<Longrightarrow> {of_nat n..+size_td d} \<subseteq> {of_nat m..+size_td_list t}"
  apply(frule td_set_list_offset_le)
  apply(drule td_set_list_offset_size_m)
  apply clarsimp
  apply(drule intvlD, clarsimp)
  apply(clarsimp simp: intvl_def)
  subgoal for k
    apply(rule exI [where x="k + n - m"])
    apply simp
    done
  done

lemma td_set_tuple_intvl_sub:
  "(d,n) \<in> td_set_tuple t m \<Longrightarrow> {of_nat n..+size_td d} \<subseteq> {of_nat m..+size_td_tuple t}"
  apply(frule td_set_tuple_offset_le)
  apply(drule td_set_tuple_offset_size_m)
  apply clarsimp
  apply(drule intvlD, clarsimp)
  apply(clarsimp simp: intvl_def)
  subgoal for k
    apply(rule exI [where x="k + n - m"])
    apply simp
    done
  done

lemma intvl_inter_le:
  assumes inter: "a + of_nat k = c + of_nat ka" and lt_d: "ka < d" and lt_ka: "k \<le> ka"
  shows "a \<in> {c..+d}"
proof -
  from lt_ka inter have "a = c + of_nat (ka - k)" by (simp add: field_simps)
  moreover from lt_d have "ka - k < d" by simp
  ultimately show ?thesis by (force simp: intvl_def)
qed

lemma intvl_inter:
  assumes nondisj: "{a..+b} \<inter> {c..+d} \<noteq> {}"
  shows "a \<in> {c..+d} \<or> c \<in> {a..+b}"
proof -
  from nondisj obtain k ka where "a + of_nat k = c + of_nat ka"
    and "k < b" and "ka < d" by (force simp: intvl_def)
  thus ?thesis by (force intro: intvl_inter_le)
qed

lemma init_intvl_disj:
  "k + z < addr_card \<Longrightarrow> {(p::addr)+of_nat k..+z} \<inter> {p..+k} = {}"
  apply(cases "k \<noteq> 0"; simp)
  apply(rule ccontr)
  apply(drule intvl_inter)
  apply(erule disjE)
   apply(drule intvlD, clarsimp)
   apply(metis add_lessD1 len_of_addr_card less_trans mod_less order_less_irrefl unat_of_nat)
  apply(drule intvlD, clarsimp)
  apply(subst (asm) Abs_fnat_homs)
  apply(subst (asm) Word.of_nat_0)
  apply(subst (asm) len_of_addr_card)
  apply clarsimp
  subgoal for k' q
    apply(cases q; simp)
    done
  done

lemma final_intvl_disj:
  "\<lbrakk> k + z \<le> n; n < addr_card \<rbrakk> \<Longrightarrow>
      {(p::addr)+of_nat k..+z} \<inter> {p+(of_nat k + of_nat z)..+n - (k+z)} = {}"
  apply(cases "z \<noteq> 0"; simp)
  apply(rule ccontr)
  apply(drule intvl_inter)
  apply(erule disjE)
   apply(drule intvlD, clarsimp)
   apply(subst (asm) Abs_fnat_homs)
   apply(subst (asm) Word.of_nat_0)
   apply(subst (asm) len_of_addr_card)
   apply clarsimp
  subgoal for k' q
    apply(cases q; simp)
    done
  apply(drule intvlD, clarsimp)
  apply(subst (asm) word_unat.norm_eq_iff [symmetric])
  apply(subst (asm) len_of_addr_card)
  apply simp
  done

lemma fa_fu_lookup_disj_inter:
  "\<forall>f m d n f' d' n'. field_lookup t f m = Some (d,n) \<longrightarrow>
      field_lookup t f' m = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd t \<longrightarrow> size_td t < addr_card \<longrightarrow>
      {(of_nat n)::addr..+size_td (d::('a,'b) typ_info)} \<inter> {of_nat n'..+size_td d'} = {}"
  "\<forall>f m d n f' m d' n'. field_lookup_struct st f m = Some (d,n) \<longrightarrow>
      field_lookup_struct st f' m = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd_struct st \<longrightarrow> size_td_struct st < addr_card \<longrightarrow>
      {(of_nat n)::addr..+size_td (d::('a,'b) typ_info)} \<inter> {of_nat n'..+size_td d'} = {}"
  "\<forall>f m d n f' m d' n'. field_lookup_list ts f m = Some (d,n) \<longrightarrow>
      field_lookup_list ts f' m = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd_list ts \<longrightarrow> size_td_list ts < addr_card \<longrightarrow>
      {(of_nat n)::addr..+size_td (d::('a,'b) typ_info)} \<inter> {of_nat n'..+size_td d'} = {}"
  "\<forall>f m d n f' m d' n'. field_lookup_tuple x f m = Some (d,n) \<longrightarrow>
      field_lookup_tuple x f' m = Some (d',n') \<longrightarrow> disj_fn f f' \<longrightarrow>
      wf_fd_tuple x \<longrightarrow> size_td_tuple x < addr_card \<longrightarrow>
      {(of_nat n)::addr..+size_td (d::('a,'b) typ_info)} \<inter> {of_nat n'..+size_td d'} = {}"
proof(induct t and st and ts and x)
  case (TypDesc nat typ_struct list)
  then show ?case by (clarsimp simp: disj_fn_def)
next
  case (TypScalar nat1 nat2 a)
  then show ?case by (clarsimp simp: disj_fn_def)
next
  case (TypAggregate list)
  then show ?case by (clarsimp simp: disj_fn_def)
next
  case Nil_typ_desc
  then show ?case by (clarsimp simp: disj_fn_def)
next
  case (Cons_typ_desc dt_tuple list)
  then show ?case 
    apply (clarsimp simp: disj_fn_def)
    apply(rule set_eqI)
    apply(clarsimp split: option.splits)
       apply fastforce
      apply(drule td_set_list_field_lookup_listD)
      apply(drule td_set_list_intvl_sub)
      apply(drule td_set_tuple_field_lookup_tupleD)
      apply(drule td_set_tuple_intvl_sub)
      apply (cases dt_tuple)
      apply(fastforce dest: init_intvl_disj)
     apply(drule td_set_list_field_lookup_listD)
     apply(drule td_set_list_intvl_sub)
     apply(drule td_set_tuple_field_lookup_tupleD)
     apply(drule td_set_tuple_intvl_sub)
     apply (cases dt_tuple)
     apply(fastforce dest: init_intvl_disj)
    apply fastforce
    done
next
  case (DTuple_typ_desc typ_desc list b)
  then show ?case 
    apply (clarsimp simp: disj_fn_def)
    apply(rule set_eqI, clarsimp)
    subgoal for f d n f' m d' n' x
      apply(cases f; clarsimp)
      apply(cases f'; clarsimp)
      apply(fastforce simp: disj_fn_def)
      done
    done
qed

lemma fa_fu_lookup_disj_interD:
  "\<lbrakk> field_lookup t f m = Some (d,n); field_lookup t f' m = Some (d',n');
      disj_fn f f'; wf_fd t; size_td t < addr_card \<rbrakk> \<Longrightarrow>
      {(of_nat n)::addr..+size_td (d::('a,'b) typ_info)} \<inter> {of_nat n'..+size_td d'} = {}"
  using fa_fu_lookup_disj_inter(1) [of t] by clarsimp

lemma fa_fu_lookup_disj_inter_listD:
  "\<lbrakk> field_lookup_list ts f m = Some (d,n);
      field_lookup_list ts f' m = Some (d',n'); disj_fn f f';
      wf_fd_list ts; size_td_list ts < addr_card \<rbrakk> \<Longrightarrow>
      {(of_nat n)::addr..+size_td (d::('a,'b) typ_info)} \<inter>
          {of_nat n'..+size_td d'} = {}"
  using fa_fu_lookup_disj_inter(3) [of ts] by clarsimp

lemma (in mem_type_sans_size) upd_rf:
  "length bs = size_of TYPE('a) \<Longrightarrow>
      update_ti_t (typ_info_t TYPE('a)) bs v
          = update_ti_t (typ_info_t TYPE('a)) bs w"
  by (simp add: upd)

lemma (in mem_type_sans_size) inv:
  "length bs = size_of TYPE('a) \<Longrightarrow>
      from_bytes (to_bytes (x::'a) bs) = x"
  unfolding from_bytes_def to_bytes_def
  by (metis fd_cons_def fd_cons_desc_def fd_cons_update_access_def field_desc.simps(1) 
      field_desc.simps(2) field_desc_def local.len local.size_of_fold 
      local.to_bytes_def local.upd local.wf_fd wf_fd_consD)

lemma (in mem_type) align:
  "align_of (TYPE('a)) dvd addr_card"
proof -
  have *: "align_of TYPE('a) < addr_card"
    by (smt (verit, best) int_dvd_int_iff less_imp_of_nat_less local.align_size_of
        local.max_size local.sz_nzero of_nat_0_less_iff of_nat_less_imp_less zdvd_not_zless)
  from * show ?thesis
    apply -
    apply(subst (asm) align_of_def)
    apply(clarsimp simp: dvd_def align_of_def)
    apply(rule exI [where x="2^(len_of TYPE(addr_bitsize) - align_td (typ_info_t TYPE('a)))"])
    apply clarsimp
    subgoal premises prems
    proof -

      from prems 
      have "align_td (typ_info_t TYPE('a)) < addr_bitsize"
        apply -
        apply(rule power_less_imp_less_exp [where a="2"]; simp add: addr_card)
        done
      then show ?thesis
        apply(simp add: addr_card flip: power_add)
        done
    qed
    done
qed

lemma (in mem_type) to_bytes_inj:
  "to_bytes (v::'a) = to_bytes (v'::'a) \<Longrightarrow> v=v'"
  apply (drule fun_cong [where x="replicate (size_of TYPE('a)) 0"])
  apply (drule arg_cong [where f="from_bytes::byte list \<Rightarrow> 'a"])
  apply (simp add: inv)
  done

lemmas unat_simps = unat_simps' max_size

lemmas (in mem_type) mem_type_simps [simp] = inv len sz_nzero max_size align
lemmas mem_type_simps [simp] = inv len sz_nzero max_size align

lemma (in mem_type) ptr_aligned_plus:
  assumes aligned: "ptr_aligned (p::'a ptr) "
  shows "ptr_aligned (p +\<^sub>p i)"
proof -
  have "int (align_of TYPE('a)) dvd (i * int (size_of TYPE('a)))"
    by (simp add: align_size_of)
  with aligned show ?thesis
    apply (cases p, simp add: ptr_aligned_def ptr_add_def scast_id)
    apply (simp only: unat_simps len_signed)
    apply (metis align align_size_of dvd_add dvd_mod dvd_mult2 mult.commute)
    done
qed


lemma (in mem_type) mem_type_self [simp]:
  "ptr_val (p::'a ptr) \<in> {ptr_val p..+size_of TYPE('a)}"
  by (rule intvl_self, rule sz_nzero)

lemma (in mem_type) intvl_Suc_nmem [simp]:
  "(p::addr) \<notin> {p + 1..+size_of TYPE('a) - Suc 0}"
  by (rule intvl_Suc_nmem', subst len_of_addr_card, rule max_size)

lemma (in mem_type) wf_size_desc_typ_uinfo_t_simp [simp]:
  "wf_size_desc (typ_uinfo_t TYPE('a))"
  by (simp add: typ_uinfo_t_def export_uinfo_def wf_size_desc_map)


lemma aggregate_map [simp]:
  "aggregate (map_td f g t) = aggregate t"
  apply(cases t)
  subgoal for x1 st n
    apply(cases st; simp)
    done
  done


lemma (in simple_mem_type) simple_tag_not_aggregate2 [simp]:
  "typ_uinfo_t TYPE('a) \<noteq> TypDesc algn (TypAggregate ts) tn"
  by (metis aggregate.simps aggregate_map aggregate_struct.simps(2) export_uinfo_def
      local.simple_tag local.typ_uinfo_t_def)

lemma (in simple_mem_type) simple_tag_not_aggregate3 [simp]:
  "typ_info_t TYPE('a) \<noteq> TypDesc algn (TypAggregate ts) tn"
  by (metis aggregate.simps aggregate_struct.simps(2) simple_tag)

lemma (in mem_type) field_of_t_mem:
  "field_of_t (p::'a ptr) (q::'b::mem_type ptr) \<Longrightarrow>
   ptr_val p \<in> {ptr_val q..+size_of TYPE('b)}"
  apply(clarsimp simp: field_of_t_def field_of_def intvl_def)
  apply(rule exI [where x="unat (ptr_val p - ptr_val q)"])
  apply simp
  apply(drule td_set_offset_size)
  apply(clarsimp simp: size_of_def)
  by (metis (mono_tags, lifting) add_leD2 add_le_same_cancel2 c_type_class.size_of_def
      leD local.size_of_def local.sz_nzero nat_less_le)

lemma map_td_map:
  "map_td f p (map_td g q t) = map_td (\<lambda>n algn. f n algn o g n algn) (p o q) t"
  "map_td_struct f p (map_td_struct g q st) = map_td_struct (\<lambda>n algn. f n algn o g n algn) (p o q) st"
  "map_td_list f p (map_td_list g q ts) = map_td_list (\<lambda>n algn. f n algn o g n algn) (p o q) ts"
  "map_td_tuple f p (map_td_tuple g q x) = map_td_tuple (\<lambda>n algn. f n algn o g n algn) (p o q) x"
  by (induct t and st and ts and x) auto

lemma field_of_t_simple:
  "field_of_t p (x::'a::simple_mem_type ptr) \<Longrightarrow> ptr_val p = ptr_val x"
  apply(clarsimp simp: field_of_t_def)
  apply(cases "typ_uinfo_t TYPE('a)")
  subgoal for x1 st n

    apply(cases st; clarsimp)
    apply(clarsimp simp: field_of_def unat_eq_zero)
    done
  done

lemma fold_td'_unfold:
 "fold_td' t =
    (let (f,s) = t in
     case s of TypDesc algn' st nm \<Rightarrow>
       (case st of
          TypScalar n algn d \<Rightarrow> d
        | TypAggregate ts \<Rightarrow> f nm (map (\<lambda>x. case x of DTuple t n d \<Rightarrow> (fold_td' (f,t),n)) ts)))"
  apply (cases t, simp)
  subgoal for a b
    apply (cases b, simp)
    done
  done

lemma fold_td_alt_def':
  "fold_td f t = (case t of
                    TypDesc algn' st nm \<Rightarrow>
                      (case st of
                         TypScalar n algn d \<Rightarrow> d
                       | TypAggregate ts \<Rightarrow> f nm (map (\<lambda>x. (fold_td f (dt_fst x),dt_snd x)) ts)))"
  apply(cases t)
  apply(clarsimp split: typ_desc.split typ_struct.splits dt_tuple.splits)
  by (metis (no_types, lifting) dt_tuple.case dt_tuple.collapse)

lemma fold_td_alt_def:
  "fold_td f t \<equiv> (case t of
                    TypDesc algn' st nm \<Rightarrow>
                      (case st of
                         TypScalar n algn d \<Rightarrow> d
                       | TypAggregate ts \<Rightarrow> f nm (map (\<lambda>x. (fold_td f (dt_fst x),dt_snd x)) ts)))"
  by (fastforce simp: fold_td_alt_def' simp del: fold_td_def)


lemma map_td'_map':
  "map_td f g t = (map_td' ((f,g),t))"
  "TypDesc algn (map_td_struct f g st) (typ_name t) = (map_td' ((f,g),TypDesc algn st (typ_name t)))"
  "TypDesc algn (TypAggregate (map_td_list f g ts)) (typ_name t) = map_td' ((f,g),TypDesc algn (TypAggregate ts) (typ_name t))"
  "map_td_tuple f g x = DTuple (map_td' ((f,g),dt_fst x)) (dt_snd x) (g (dt_trd x))"
  by (induct t and st and ts and x) (auto simp: split_DTuple_all)

lemma map_td'_map:
  "map_td f g t = (case t of TypDesc algn st nm \<Rightarrow> TypDesc algn (case st of
           TypScalar n algn d \<Rightarrow> TypScalar n algn (f n algn d) |
           TypAggregate ts \<Rightarrow> TypAggregate (map (\<lambda>x. DTuple (map_td f g (dt_fst x)) (dt_snd x) (g (dt_trd x))) ts)) nm)"
  apply(subst map_td'_map')
  apply(subst map_td'_map')
  apply(cases t, simp add: typ_struct.splits)
  apply(auto simp: split_DTuple_all)
  done

lemma map_td_alt_def:
  "map_td f g t \<equiv> (case t of TypDesc algn st nm \<Rightarrow> TypDesc algn (case st of
           TypScalar n algn d \<Rightarrow> TypScalar n algn (f n algn d) |
           TypAggregate ts \<Rightarrow> TypAggregate (map (\<lambda>x. DTuple (map_td f g (dt_fst x)) (dt_snd x) (g (dt_trd x))) ts)) nm)"
  by (simp add: map_td'_map)

lemma size_td_fm':
  "size_td (t::('a,'b) typ_desc) = fold_td tnSum (map_td (\<lambda>n x d. n) g t)"
  "size_td_struct (st::('a,'b) typ_struct) = fold_td_struct (typ_name t) tnSum (map_td_struct (\<lambda>n x d. n) g st)"
  "size_td_list (ts::('a,'b) typ_tuple list) = fold_td_list (typ_name t) tnSum (map_td_list (\<lambda>n x d. n) g ts)"
  "size_td_tuple (x::('a,'b) typ_tuple) = fold_td_tuple tnSum (map_td_tuple (\<lambda>n x d. n) g x)"
  by  (induct t and st and ts and x) (auto simp: tnSum_def split: dt_tuple.splits)

lemma size_td_fm:
  "size_td (t::('a,'b) typ_desc) \<equiv> fold_td tnSum (map_td (\<lambda>n algn d. n) id t)"
  using size_td_fm'(1) [of t id] by clarsimp

lemma align_td_wo_align_fm':
  "align_td_wo_align (t::('a,'b) typ_desc) = fold_td tnMax (map_td (\<lambda>n x d. x) g t)"
  "align_td_wo_align_struct (st::('a,'b) typ_struct) = fold_td_struct (typ_name t) tnMax (map_td_struct (\<lambda>n x d. x) g st)"
  "align_td_wo_align_list (ts::('a,'b) typ_tuple list) = fold_td_list (typ_name t) tnMax (map_td_list (\<lambda>n x d. x) g ts)"
  "align_td_wo_align_tuple (x::('a,'b) typ_tuple) = fold_td_tuple tnMax (map_td_tuple (\<lambda>n x d. x) g x)"
  by (induct t and st and ts and x) (auto simp: tnMax_def split: dt_tuple.splits)

lemma align_td_wo_align_fm:
  "align_td_wo_align (t::('a,'b) typ_desc) \<equiv> fold_td tnMax (map_td (\<lambda>n algn d. algn) id t)"
  using align_td_wo_align_fm'(1) [of t id] by clarsimp

thm case_dt_tuple_def

lemma case_dt_tuple:
  "snd ` case_dt_tuple (\<lambda>t n d. Pair (f t) n) ` X = dt_snd ` X"
  by (force simp: image_iff split_DTuple_all split: dt_tuple.splits)

lemma map_DTuple_dt_snd:
  "map_td_tuple f g x = DTuple a b c \<Longrightarrow> b = dt_snd x"
  by (metis dt_tuple.inject map_td'_map'(4))

lemma wf_desc_fm':
  "wf_desc (t::('a,'b) typ_desc) = fold_td wfd (map_td (\<lambda>n x d. True) g t)"
  "wf_desc_struct (st::('a,'b) typ_struct) = fold_td_struct (typ_name t) wfd (map_td_struct (\<lambda>n x d. True) g st)"
  "wf_desc_list (ts::('a,'b) typ_tuple list) = fold_td_list (typ_name t) wfd (map_td_list (\<lambda>n x d. True) g ts)"
  "wf_desc_tuple (x::('a,'b) typ_tuple) = fold_td_tuple wfd (map_td_tuple (\<lambda>n x d. True) g x)"
  supply split_DTuple_all[simp] dt_tuple.splits[split]
  apply (induct t and st and ts and x, all \<open>clarsimp simp: wfd_def image_comp[symmetric]\<close>)
  apply (rule iffI; clarsimp)
   apply (metis (no_types) dt_prj_simps(2) dt_snd_map_td_list imageI)
  by (metis (mono_tags) case_dt_tuple dt_prj_simps(2) dt_snd_map_td_list image_eqI)

lemma wf_desc_fm:
  "wf_desc (t::('a,'b) typ_desc) \<equiv> fold_td wfd (map_td (\<lambda>n algn d. True) id t)"
  using wf_desc_fm'(1) [of t id] by auto

lemma update_tag_list_empty [simp]:
  "(map_td_list f g xs = []) = (xs = [])"
  by (cases xs, auto)

lemma wf_size_desc_fm':
  "wf_size_desc (t::('a,'b) typ_desc) = fold_td wfsd (map_td (\<lambda>n x d. 0 < n) g t)"
  "wf_size_desc_struct (st::('a,'b) typ_struct) = fold_td_struct (typ_name t) wfsd (map_td_struct (\<lambda>n x d. 0 < n) g st)"
  "ts \<noteq> [] \<longrightarrow> wf_size_desc_list (ts::('a,'b) typ_tuple list) = fold_td_list (typ_name t) wfsd (map_td_list (\<lambda>n x d. 0 < n) g ts)"
  "wf_size_desc_tuple (x::('a,'b) typ_tuple) = fold_td_tuple wfsd (map_td_tuple (\<lambda>n x d. 0 < n) g x)"
  by (induct t and st and ts and x) (auto simp: wfsd_def split: dt_tuple.splits)

lemma wf_size_desc_fm:
  "wf_size_desc (t::('a,'b) typ_desc) \<equiv> fold_td wfsd (map_td (\<lambda>n algn d. 0 < n) id t)"
  using wf_size_desc_fm'(1) [of t id] by auto

typedef stack_byte = "UNIV::byte set"
  by (simp)

definition "stack_byte_name = ''stack_byte''"

instantiation stack_byte :: c_type
begin

definition "typ_name_itself (x::stack_byte itself) = stack_byte_name"

definition
  typ_info_stack_byte: "typ_info_t (x::stack_byte itself) \<equiv>
     TypDesc 0 (TypScalar 1 0
              \<lparr>field_access = \<lambda>v bs. [Rep_stack_byte v],
               field_update = \<lambda>bs v. if length bs \<ge> 1 then Abs_stack_byte (hd bs) else Abs_stack_byte (0::byte),
               field_sz = 1\<rparr>)
            stack_byte_name"

instance
  by (intro_classes) (simp add: typ_name_itself_stack_byte_def typ_info_stack_byte)
end

lemma size_of_stack_byte [simp]:
  "size_of TYPE(stack_byte) = 1"
  "size_td (typ_info_t TYPE(stack_byte)) = 1"
  "size_td (typ_uinfo_t TYPE(stack_byte)) = 1"
  by (simp_all add: size_of_def typ_info_stack_byte typ_uinfo_t_def)

lemma align_of_stack_byte [simp]:
  "align_of TYPE(stack_byte) = 1"
  "align_td (typ_info_t TYPE(stack_byte)) = 0"
  "align_td (typ_uinfo_t TYPE(stack_byte)) = 0"
  by (simp_all add: align_of_def typ_info_stack_byte typ_uinfo_t_def)

lemma length_1_conv: "length bs = Suc 0 \<longleftrightarrow> (\<exists>b. bs = [b])"
  by (cases bs) auto
lemma padding_lense_stack_byte: "padding_lense (\<lambda>v bs. [Rep_stack_byte v])
     (\<lambda>bs v.
         if Suc 0 \<le> length bs then Abs_stack_byte (hd bs) else Abs_stack_byte 0)
     (Suc 0)"
  apply (unfold_locales)
        apply (simp add: padding_base.is_padding_byte_def padding_base.is_value_byte_def Abs_stack_byte_inverse )
    subgoal

      proof -
        have "length [1::8 word] = Suc 0"
          by simp
        then show ?thesis
          by (metis (mono_tags, opaque_lifting) Abs_stack_byte_inject One_nat_def
              Rep_stack_byte_inject UNIV_I hd_conv_nth length_append n_not_Suc_n
              plus_1_eq_Suc self_append_conv2 zero_neq_one)
      qed
           apply (clarsimp)
          apply clarsimp
         apply (clarsimp simp add: Rep_stack_byte_inverse)
        apply simp
       apply simp
      apply simp
      done

instantiation stack_byte:: xmem_contained_type
begin
instance
  apply (intro_classes)
              apply (simp add: typ_info_stack_byte)
             apply (simp add: typ_info_stack_byte)
            apply (simp add: typ_info_stack_byte wf_lf_def fd_cons_desc_def fd_cons_double_update_def
                    fd_cons_update_access_def fd_cons_access_update_def
                    Rep_stack_byte_inverse fd_cons_length_def)
           apply (simp add: typ_info_stack_byte)
          apply simp
         apply (simp add: typ_info_stack_byte align_field_def)
        apply (simp add: typ_info_stack_byte)
       apply (simp add: addr_card)
      apply (simp add: typ_info_stack_byte)
     apply (simp add: typ_info_stack_byte)
    apply (simp add: typ_info_stack_byte wf_field_desc_def padding_lense_stack_byte)
   apply  (simp add: typ_info_stack_byte)
  apply  (simp add: typ_info_stack_byte)
  done

end

end
