theory Abs_Rename_LMS_Verification
  imports "../abs-def/Abs_SAIS"

begin

section "Rename Mapping Proofs"

lemma abs_rename_mapping'_length:
  "length (abs_rename_mapping' T LMS names i) = length names"
  by (induct rule: abs_rename_mapping'.induct[of _ T LMS names i]; simp)

lemma abs_rename_mapping_length:
  "length (abs_rename_mapping T LMS) = length T"
  by (clarsimp simp: abs_rename_mapping_def abs_rename_mapping'_length)

lemma rename_mapping'_unchanged:
  "\<lbrakk>x \<notin> set LMS; x < length names\<rbrakk> \<Longrightarrow>
    (abs_rename_mapping' T LMS names i) ! x = names ! x"
  by (induct rule: abs_rename_mapping'.induct[of _ T LMS names i]; simp)

(*
lemma rename_mapping'_bounds:
  "\<lbrakk>x \<in> set LMS; Max (set LMS) < length names; distinct LMS\<rbrakk> \<Longrightarrow>
   (rename_mapping' T LMS names i) ! x < i + length LMS"
  apply (induct rule: rename_mapping'.induct[of _ T LMS names i]; simp)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (erule disjE)
    apply (clarsimp simp: rename_mapping'_unchanged)
   apply clarsimp
  apply clarsimp
  apply (erule disjE)
   apply (clarsimp simp: rename_mapping'_unchanged)
  apply clarsimp
  done
*)

lemma rename_mapping'_lms:
  assumes "distinct LMS"
  and     "ordlistns.sorted (map (lms_slice T) LMS)"
  and     "i \<in> set LMS"
  and     "i < length names"
shows     "(abs_rename_mapping' T LMS names j) ! i =
           j + (ordlistns.elem_rank ((lms_slice T) ` set LMS) (lms_slice T i))"
  using assms
proof (induct arbitrary: i rule: abs_rename_mapping'.induct[of _ T LMS names j])
  case (1 uu names uv)
  then show ?case
    by force
next
  case (2 uw x names j)
  note A = this
  hence "x = i"
    by force
  hence "lms_slice uw ` set [x] = {lms_slice uw i}"
    using A(1) by auto
  hence "ordlistns.elem_rank (lms_slice uw ` set [x]) (lms_slice uw i) = 0"
    by (simp add: ordlistns.elem_rank_def elm_rank_def)
  then show ?case
    by (simp add: \<open>x = i\<close> A(4))
next
  case (3 T a b xs names j)
  note IH = this

  have A1: "distinct (b # xs)"
    using IH(3) by fastforce

  have A2: "ordlistns.sorted (map (lms_slice T) (b # xs))"
    using IH(4) by fastforce

  have A3: "i < length (names[a := j])"
    by (simp add: IH(6))

  have A4: "a \<notin> set (b # xs)"
    using IH(3) by auto

  have A5: "ordlistns.elem_rank (lms_slice T ` set (a # b # xs)) (lms_slice T a) = 0"
    unfolding ordlistns.elem_rank_def elm_rank_def using IH(4) by auto

  note IH1 = IH(1)[OF _ A1 A2 _ A3]
  note IH2 = IH(2)[OF _ A1 A2 _ A3]

  have P: "i \<in> set (b # xs) \<or> i = a"
    using IH(5) by force

  have "lms_slice T a = lms_slice T b \<or>
        lms_slice T a \<noteq> lms_slice T b"
    by blast
  then show ?case
  proof
    assume B: "lms_slice T a = lms_slice T b"
    hence C: "abs_rename_mapping' T (a # b # xs) names j =
              abs_rename_mapping' T (b # xs) (names[a := j]) j"
      by simp

    from IH1[OF B] C
    have "i \<in> set (b # xs) \<Longrightarrow> ?thesis"
      by (simp add: B list.set_map)
    moreover
    from rename_mapping'_unchanged[OF A4, of "names[a := j]" T j, simplified C[symmetric]] IH(6) A5
    have "i = a \<Longrightarrow> ?thesis"
      by simp
    moreover
    note P
    ultimately show ?thesis
      by blast
  next
    assume B: "lms_slice T a \<noteq> lms_slice T b"
    hence C: "abs_rename_mapping' T (a # b # xs) names j =
              abs_rename_mapping' T (b # xs) (names[a := j]) (Suc j)"
      by simp

    have D: "lms_slice T a \<notin> lms_slice T ` set (b # xs)"
    proof
      assume "lms_slice T a \<in> lms_slice T ` set (b # xs)"
      moreover
      from IH(4) ordlistns.sorted_simps(2)[of "lms_slice T a" "map (lms_slice T) (b # xs)"]
      have "\<forall>y \<in> set (map (lms_slice T) (b # xs)). list_less_eq_ns (lms_slice T a) y"
        by auto
      ultimately show False
        using A2 B by auto
    qed

    from rename_mapping'_unchanged[OF A4, of "names[a := j]" T "Suc j", simplified C[symmetric]]
    have "i = a \<Longrightarrow> ?thesis"
      using A5 IH(6) by auto
    moreover
    have "i \<in> set (b # xs) \<Longrightarrow> ?thesis"
    proof -
      assume "i \<in> set (b # xs)"
      with IH2[OF B, simplified C[symmetric]] C
      have "abs_rename_mapping' T (a # b # xs) names j ! i =
            j + Suc (ordlistns.elem_rank (lms_slice T ` set (b # xs)) (lms_slice T i))"
        by linarith
      moreover
      have "lms_slice T ` set (a # b # xs) =
            insert (lms_slice T a) (lms_slice T ` set (b # xs))"
        by simp
      moreover
      have "ordlistns.elem_rank (insert (lms_slice T a) (lms_slice T ` set (b # xs)))
              (lms_slice T i) =
            Suc (ordlistns.elem_rank (lms_slice T ` set (b # xs)) (lms_slice T i))"
      proof (intro ordlistns.elem_rank_insert_min)
        from D
        show "lms_slice T a \<notin> lms_slice T ` set (b # xs)" .
      next
        show "finite (lms_slice T ` set (b # xs))"
          by blast
      next
        show "\<forall>y\<in>lms_slice T ` set (b # xs). list_less_ns (lms_slice T a) y"
          using D IH(4) by fastforce
      next
        show "lms_slice T i \<in> lms_slice T ` set (b # xs)"
          using \<open>i \<in> set (b # xs)\<close> by blast
      qed
      ultimately show ?thesis
        by presburger
    qed
    moreover
    note P
    ultimately show ?thesis
      by blast
  qed
qed

lemma abs_rename_mapping_lms:
  assumes "distinct LMS"
  and     "ordlistns.sorted (map (lms_slice T) LMS)"
  and     "i \<in> set LMS"
  and     "i < length T"
shows     "(abs_rename_mapping T LMS) ! i =
           ordlistns.elem_rank ((lms_slice T) ` set LMS) (lms_slice T i)"
  unfolding abs_rename_mapping_def
  using rename_mapping'_lms[where j = 0, simplified, OF assms(1-3)] assms(4)
        abs_rename_mapping_length[of T LMS]
  by auto
(*
lemma rename_mapping'_first_item:
  assumes "x \<notin> set LMS"
  and     "x < length names"
shows "rename_mapping' T (x # LMS) names k ! x = k"
proof (rule rename_mapping'.cases[of "(T, x # LMS, names, k)"]; clarsimp)
  from `x < length names`
  show "names[x := k] ! x = k"
    by simp
next
  fix y ys
  assume "LMS = y # ys"

  from rename_mapping'_unchanged[OF `x \<notin> set LMS`, of "names[x := k]" T k]
       `x < length names`
       `LMS = y # ys`
  have R1: "rename_mapping' T (y # ys) (names[x := k]) k ! x = k"
    by simp

  from rename_mapping'_unchanged[OF `x \<notin> set LMS`, of "names[x := k]" T "Suc k"]
       `x < length names`
       `LMS = y # ys`
  have R2: "rename_mapping' T (y # ys) (names[x := k]) (Suc k) ! x = k"
    by simp

  from R1 R2
  show
    "(lms_slice T x = lms_slice T y \<longrightarrow>
        rename_mapping' T (y # ys) (names[x := k]) k ! x = k) \<and>
     (lms_slice T x \<noteq> lms_slice T y \<longrightarrow>
        rename_mapping' T (y # ys) (names[x := k]) (Suc k) ! x = k)"
    by simp
qed

lemma abs_rename_mapping_first_item:
  assumes "distinct LMS"
  and     "LMS \<noteq> []"
  and     "LMS ! 0 < length T"
shows "(rename_mapping T LMS) ! (LMS ! 0) = 0"
proof (cases LMS)
  case Nil
  then show ?thesis
    using assms by blast
next
  case (Cons a list)
  then show ?thesis
    unfolding abs_rename_mapping_def
    using assms
    by (simp add: rename_mapping'_first_item)
qed
*)

lemma abs_rename_mapping_lms_all:
  assumes "distinct LMS"
  and     "ordlistns.sorted (map (lms_slice T) LMS)"
  and     "\<forall>x \<in> set LMS. x < length T"
shows "\<forall>x \<in> set LMS. (!) (abs_rename_mapping T LMS) x =
                     ordlistns.elem_rank (lms_slice T ` set LMS) (lms_slice T x)"
  using assms(1) assms(2) assms(3) abs_rename_mapping_lms by blast

lemma map_abs_rename_mapping:
  assumes "distinct LMS"
  and     "ordlistns.sorted (map (lms_slice T) LMS)"
  and     "\<forall>x \<in> set LMS. x < length T"
  and     "set xs \<subseteq> set LMS"
shows "map ((!) (abs_rename_mapping T LMS)) xs =
       map (ordlistns.elem_rank (lms_slice T ` set LMS)) (map (lms_slice T) xs)"
  using assms(1) assms(2) assms(3) assms(4) abs_rename_mapping_lms_all by fastforce

section "Rename String Proofs"

lemma rename_list_length:
  "length (rename_string xs names) = length xs"
  by (induct xs; simp)

theorem rename_list_correct:
  "rename_string T names = map (\<lambda>x. names ! x) T"
  by (induct T; simp)

corollary rename_list_nth:
  "i < length T \<Longrightarrow> (rename_string T names) ! i = names ! (T ! i)"
  by (simp add: rename_list_correct)

end