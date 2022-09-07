(* Title: thys/Numerals.thy
   Author: Jian Xu, Xingyuan Zhang, and Christian Urban
   Modifications: Sebastiaan Joosten
 
   Further contributions by Franz Regensburger (FABR) 02/2022 :
   - Re-ordering of sections
 *)

section \<open>Encoding of Natural Numbers\<close>

theory Numerals
  imports ComposedTMs BlanksDoNotMatter
begin

subsection \<open>A class for generating numerals\<close>

class tape =
  fixes tape_of :: "'a \<Rightarrow> cell list" ("<_>" 100)


instantiation nat::tape begin
definition tape_of_nat where "tape_of_nat (n::nat) \<equiv> Oc \<up> (Suc n)"
instance by standard
end

type_synonym nat_list = "nat list"

instantiation list::(tape) tape begin
(* fun tape_of_nat_list :: "nat list \<Rightarrow> cell list"
   The type ('a::tape) list is needed for lemma tape_of_list_empty in Abacus_Mopup
 *)
fun tape_of_nat_list :: "('a::tape) list \<Rightarrow> cell list"
  where 
    "tape_of_nat_list [] = []" |
    "tape_of_nat_list [n] = <n>" |
    "tape_of_nat_list (n#ns) = <n> @ Bk # (tape_of_nat_list ns)"
definition tape_of_list where "tape_of_list \<equiv> tape_of_nat_list"
instance by standard
end

instantiation prod:: (tape, tape) tape begin
fun tape_of_nat_prod :: "('a::tape) \<times> ('b::tape) \<Rightarrow> cell list" 
  where "tape_of_nat_prod (n, m) = <n> @ [Bk] @ <m>" 
definition tape_of_prod where "tape_of_prod \<equiv> tape_of_nat_prod"
instance by standard
end

subsection \<open>Some lemmas about numerals used for rewriting\<close>

(* Lemma tape_of_list_empty is needed in Abacus_Mopup.thy *)

lemma tape_of_list_empty[simp]: "<[]> = ([]::cell list)" by (simp add: tape_of_list_def)

lemma tape_of_nat_list_cases2: "<(nl::nat list)> = [] \<or> (\<exists>r'. <nl> = Oc # r')"
  by (induct rule: tape_of_nat_list.induct)(auto simp add: tape_of_nat_def tape_of_list_def)

subsection \<open>Unique decomposition of standard tapes\<close>

text \<open>Some lemmas about unique decomposition of tapes in standard halting configuration.
\<close>

lemma OcSuc_lemma: "Oc # Oc \<up> n1 = Oc \<up> n2 \<Longrightarrow> Suc n1 = n2"
proof (induct n1 arbitrary: n2)
  case 0
  then have A: "Oc # Oc \<up> 0 =  Oc \<up> n2" .
  then show ?case
  proof -
    from A have "[Oc] = Oc \<up> n2" by auto
    moreover have "[Oc] = Oc \<up> n2 \<Longrightarrow> Suc 0 = n2"
      by (induct n2)auto
    ultimately show ?case by auto
  qed
next
  fix n1 n2
  assume IV1: "\<And>n2. Oc # Oc \<up> n1 = Oc \<up> n2 \<Longrightarrow> Suc n1 = n2"
  and IV2: "Oc # Oc \<up> Suc n1 = Oc \<up> n2"
  show "Suc (Suc n1) = n2"
  proof (cases n2)
    case 0
    then have "Oc \<up> n2 = []" by auto
    with IV2 have False by auto
    then show ?thesis by auto
  next
    case (Suc n3)
    then have "n2 = Suc n3" .
    with IV2 have "Oc # Oc \<up> Suc n1 = Oc \<up> (Suc n3)" by auto
    then have "Oc # Oc # Oc \<up> n1 = Oc # Oc \<up> n3" by auto
    then have "Oc # Oc \<up> n1 = Oc \<up> n3" by auto
    with IV1 have "Suc n1 = n3" by auto
    then have "Suc (Suc n1) = Suc n3" by auto
   
    with \<open>n2 = Suc n3\<close> show ?thesis by auto
  qed
qed

lemma inj_tape_of_list: "(<n1::nat>) = (<n2::nat>) \<Longrightarrow> n1 = n2"
  by (induct n1 arbitrary: n2) (auto simp add: OcSuc_lemma tape_of_nat_def)

lemma inj_repl_Bk: "Bk \<up> k1 = Bk \<up> k2 \<Longrightarrow> k1 = k2" by auto

lemma last_of_numeral_is_Oc: "last (<n::nat>) = Oc"
  by (auto simp add: tape_of_nat_def)

lemma hd_of_numeral_is_Oc: "hd (<n::nat>) = Oc"
  by (auto simp add: tape_of_nat_def)

lemma rev_replicate: "rev (Bk \<up> l1) = (Bk \<up> l1)" by auto

lemma rev_numeral: "rev (<n::nat>) = <n::nat>"
  by (induct n)(auto simp add: tape_of_nat_def)

lemma drop_Bk_prefix: "n < l \<Longrightarrow> hd (drop n ((Bk \<up> l) @ xs)) = Bk"
  by (induct n arbitrary: l xs)(auto)

lemma unique_Bk_postfix: "<n1::nat> @ Bk \<up> l1 = <n2::nat> @ Bk \<up> l2 \<Longrightarrow> l1 = l2"
proof -
  assume "<n1::nat> @ Bk \<up> l1 = <n2::nat> @ Bk \<up> l2"
  then have "rev (<n1::nat> @ Bk \<up> l1) = rev (<n2::nat> @ Bk \<up> l2)"
    by auto
  then have "rev (Bk \<up> l1) @ rev (<n1::nat>) = rev (Bk \<up> l2) @ rev (<n2::nat>)" by auto
  then have A: "(Bk \<up> l1) @ (<n1::nat>) = (Bk \<up> l2) @ (<n2::nat>)"
    by (auto simp add: rev_replicate rev_numeral)
  then show "l1 = l2"
  proof (cases "l1 = l2")
    case True
    then show ?thesis by auto
  next
    case False
    then have "l1 < l2 \<or> l2 < l1" by auto
    then show ?thesis
    proof
      assume "l1 < l2 "
      then have False
      proof -
        have "hd (drop l1 (Bk \<up> l1) @ (<n1::nat>)) = hd ( <n1::nat>)" by auto
        also have "... = Oc" by (auto simp add: hd_of_numeral_is_Oc)
        finally have F1: "hd (drop l1 (Bk \<up> l1) @ (<n1::nat>)) =  Oc" .

        from \<open>l1 < l2\<close>have "hd (drop l1 ((Bk \<up> l2) @ (<n2::nat>))) = Bk"
          by (auto simp add: drop_Bk_prefix)
        with A have  "hd (drop l1 ((Bk \<up> l1) @ (<n1::nat>))) = Bk" by auto
        with F1 show False by auto
      qed
      then show ?thesis by auto
    next
      assume "l2 < l1"
      then have False
      proof -
        have "hd (drop l2 (Bk \<up> l2) @ (<n2::nat>)) = hd ( <n2::nat>)" by auto
        also have "... = Oc" by (auto simp add: hd_of_numeral_is_Oc)
        finally have F2: "hd (drop l2 (Bk \<up> l2) @ (<n2::nat>)) =  Oc" .

        from \<open>l2 < l1\<close> have "hd (drop l2 ((Bk \<up> l1) @ (<n1::nat>))) = Bk"
          by (auto simp add: drop_Bk_prefix)
        with A have  "hd (drop l2 ((Bk \<up> l2) @ (<n2::nat>))) = Bk" by auto
        with F2 show False by auto
      qed
      then show ?thesis by auto
    qed
  qed
qed

lemma unique_decomp_tap:
  assumes "(lx, <n1::nat> @ Bk \<up> l1) = (ly, <n2::nat> @ Bk \<up> l2)"
  shows "lx=ly \<and> n1=n2 \<and> l1=l2"
proof
  from assms show "lx = ly " by auto
next
  show "n1 = n2 \<and> l1 = l2"
  proof
    from assms have major: "<n1::nat> @ Bk \<up> l1 = <n2::nat> @ Bk \<up> l2" by auto
    then have "rev (<n1::nat> @ Bk \<up> l1) = rev (<n2::nat> @ Bk \<up> l2)"
      by auto
    then have "rev (Bk \<up> l1) @ rev (<n1::nat>) = rev (Bk \<up> l2) @ rev (<n2::nat>)" by auto
    then have A: "(Bk \<up> l1) @ (<n1::nat>) = (Bk \<up> l2) @ (<n2::nat>)"
      by (auto simp add: rev_replicate rev_numeral)
    then show "n1 = n2"
    proof -
      from major have "l1 = l2" by (rule unique_Bk_postfix)
      with A have "(<n1::nat>) = (<n2::nat>)" by auto
      then show "n1 = n2" by (rule inj_tape_of_list)
    qed
  next
    from assms have major: "<n1::nat> @ Bk \<up> l1 = <n2::nat> @ Bk \<up> l2" by auto
    then show "l1 = l2" by (rule unique_Bk_postfix)
  qed
qed

lemma unique_decomp_std_tap:
  assumes "(Bk \<up> k1, <n1::nat> @ Bk \<up> l1) = (Bk \<up> k2, <n2::nat> @ Bk \<up> l2)"
  shows "k1=k2 \<and> n1=n2 \<and> l1=l2"
proof
  from assms have "Bk \<up> k1 = Bk \<up> k2" by auto
  then show "k1 = k2" by auto
next
  show "n1 = n2 \<and> l1 = l2"
  proof
    from assms have major: "<n1::nat> @ Bk \<up> l1 = <n2::nat> @ Bk \<up> l2" by auto
    then have "rev (<n1::nat> @ Bk \<up> l1) = rev (<n2::nat> @ Bk \<up> l2)"
      by auto
    then have "rev (Bk \<up> l1) @ rev (<n1::nat>) = rev (Bk \<up> l2) @ rev (<n2::nat>)" by auto
    then have A: "(Bk \<up> l1) @ (<n1::nat>) = (Bk \<up> l2) @ (<n2::nat>)"
      by (auto simp add: rev_replicate rev_numeral)
    then show "n1 = n2"
    proof -
      from major have "l1 = l2" by (rule unique_Bk_postfix)
      with A have "(<n1::nat>) = (<n2::nat>)" by auto
      then show "n1 = n2" by (rule inj_tape_of_list)
    qed
  next
    from assms have major: "<n1::nat> @ Bk \<up> l1 = <n2::nat> @ Bk \<up> l2" by auto
    then show "l1 = l2" by (rule unique_Bk_postfix)
  qed
qed


subsection \<open>Lists of numerals never contain two consecutive blanks\<close>

definition noDblBk:: "cell list \<Rightarrow> bool"
  where "noDblBk cs \<equiv> \<forall>i. Suc i < length cs \<and> cs!i = Bk \<longrightarrow>  cs!(Suc i) = Oc"

lemma noDblBk_Bk_Oc_rep: "noDblBk (Oc \<up> n1)"
  by (simp add:  noDblBk_def )

lemma noDblBk_Bk_imp_Oc: "\<lbrakk>noDblBk cs; Suc i < length cs; cs!i = Bk \<rbrakk> \<Longrightarrow>  cs!(Suc i) = Oc"
  by (auto simp add: noDblBk_def)

lemma noDblBk_imp_noDblBk_Oc_cons: "noDblBk cs \<Longrightarrow> noDblBk (Oc#cs)"
  by (smt Suc_less_eq Suc_pred add.right_neutral add_Suc_right cell.exhaust list.size(4)
      neq0_conv noDblBk_Bk_imp_Oc noDblBk_def nth_Cons_0 nth_Cons_Suc)

lemma noDblBk_Numeral: "noDblBk (<n::nat>)"
  by (auto simp add: noDblBk_def tape_of_nat_def)

lemma noDblBk_Nil: "noDblBk []"
  by (auto simp add: noDblBk_def)

lemma noDblBk_Singleton: "noDblBk (<[n::nat]>)"
  by (auto simp add: noDblBk_def tape_of_nat_def tape_of_list_def)

(* the next two lemmas are for the inductive step in lemma noDblBk_tape_of_nat_list *)
lemma tape_of_nat_list_cons_eq:"nl \<noteq> [] \<Longrightarrow> <(a::nat) # nl> = <a> @ Bk # <nl>"
  by (metis list.exhaust tape_of_list_def tape_of_nat_list.simps(3))

lemma noDblBk_cons_cons: "noDblBk(<(x::nat) # xs>) \<Longrightarrow> noDblBk(<a::nat> @ Bk # <x # xs>)"
proof -
  assume F0: "noDblBk (<x # xs>)"
  have F1: "hd(<x # xs>) = Oc"
    by (metis hd_append hd_of_numeral_is_Oc list.sel(1)
        tape_of_nat_list_cons_eq tape_of_list_def tape_of_nat_list.simps(2)
        tape_of_nat_list_cases2)
  have F2: "<a> = Oc \<up> (Suc a)" by (auto simp add: tape_of_nat_def)
  have "noDblBk (<a::nat>)" by (auto simp add: noDblBk_Numeral)
  with F0 and F1 and F2 show ?thesis
    unfolding noDblBk_def
  proof -
    assume A1: "\<forall>i. Suc i < length (<x # xs>) \<and> <x # xs> ! i = Bk \<longrightarrow> <x # xs> ! Suc i = Oc"
      and  A2: "hd (<x # xs>) = Oc"
      and  A3: "<a> = Oc \<up> Suc a"
      and  A4: "\<forall>i. Suc i < length (<a>) \<and> <a> ! i = Bk \<longrightarrow> <a> ! Suc i = Oc"
    show   "\<forall>i. Suc i < length (<a> @ Bk # <x # xs>) \<and>
              (<a> @ Bk # <x # xs>) ! i = Bk \<longrightarrow> (<a> @ Bk # <x # xs>) ! Suc i = Oc"
    proof
      fix i
      show "Suc i < length (<a> @ Bk # <x # xs>) \<and>
                (<a> @ Bk # <x # xs>) ! i = Bk \<longrightarrow> (<a> @ Bk # <x # xs>) ! Suc i = Oc"
      proof
        assume "Suc i < length (<a> @ Bk # <x # xs>) \<and> (<a> @ Bk # <x # xs>) ! i = Bk"
        then show "(<a> @ Bk # <x # xs>) ! Suc i = Oc"
        proof
          assume A5: "Suc i < length (<a> @ Bk # <x # xs>)"
            and A6: "(<a> @ Bk # <x # xs>) ! i = Bk"
          show "(<a> @ Bk # <x # xs>) ! Suc i = Oc"
          proof -
            from A5 have "Suc i < length (<a>) \<or> Suc i =  length (<a>) \<or>
                          Suc i = Suc (length (<a>)) \<or> (Suc (length (<a>)) < Suc i \<and> Suc i < length (<a> @ Bk # <x # xs>))"
              by auto
            then show ?thesis
            proof
              assume "Suc i < length (<a>)"
              with A1 A2 A3 A4 A5 show ?thesis
                by (simp add: nth_append')
            next
              assume "Suc i = length (<a>) \<or> Suc i = Suc (length (<a>)) \<or> Suc (length (<a>)) < Suc i \<and> Suc i < length (<a> @ Bk # <x # xs>)"
              then show "(<a> @ Bk # <x # xs>) ! Suc i = Oc"
              proof
                assume "Suc i = length (<a>)"
                with A1 A2 A3 A4 A5 A6 show "(<a> @ Bk # <x # xs>) ! Suc i = Oc"
                  by (metis lessI nth_Cons_Suc nth_append' nth_append_length replicate_append_same)
              next
                assume "Suc i = Suc (length (<a>)) \<or> Suc (length (<a>)) < Suc i \<and> Suc i < length (<a> @ Bk # <x # xs>)"
                then show "(<a> @ Bk # <x # xs>) ! Suc i = Oc"
                proof 
                  assume "Suc i = Suc (length (<a>))"
                  with A1 A2 A3 A4 A5 A6 show "(<a> @ Bk # <x # xs>) ! Suc i = Oc"                  
                    by (metis One_nat_def Suc_eq_plus1 length_Cons length_append list.collapse list.size(3)
                        nat_neq_iff nth_Cons_0 nth_Cons_Suc nth_append_length_plus)
                next
                  assume A7: "Suc (length (<a>)) < Suc i \<and> Suc i < length (<a> @ Bk # <x # xs>)"
                  have F3: "(<a> @ Bk # <x # xs>) = ((<a> @ [Bk]) @ <x # xs>)" by auto

                  have F4: "\<And>n. ((<a> @ [Bk]) @ <x # xs>)! (length (<a> @ [Bk]) + n) = (<x # xs>)!n"
                    using nth_append_length_plus by blast
                  from A7 have "\<exists>m. i = Suc (length (<a>)) + m" by arith
                  then obtain m where w_m: "i = Suc (length (<a>)) + m" by blast
                  with A7 have F5: "Suc m < length (<x # xs>)" by auto
                  from w_m F4 have F6: "((<a> @ [Bk]) @ <x # xs>) ! i = (<x # xs>)! m" by auto
                  with F5 A7 have F7: "((<a> @ [Bk]) @ <x # xs>) ! (Suc i) = (<x # xs>)! (Suc m)"
                    by (metis F4 add_Suc_right length_append_singleton w_m)

                  from A6 and F6  have "(<x # xs>)! m = Bk" by auto
                  with A1 and F5 have "(<x # xs>)! (Suc m) = Oc" by auto
                  with F7 have "((<a> @ [Bk]) @ <x # xs>) ! (Suc i) = Oc" by auto
                  with F3 show "(<a> @ Bk # <x # xs>)! (Suc i) = Oc" by auto
                qed
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

theorem noDblBk_tape_of_nat_list: "noDblBk(<nl:: nat list>)"
proof (induct nl)
  case Nil
  then show ?case
    by (auto simp add: noDblBk_def tape_of_nat_def tape_of_list_def)
next
  case (Cons a nl)
  then have IV: "noDblBk (<nl>)" .
  show "noDblBk (<a # nl>)"
  proof (cases nl)
    case Nil
    then show ?thesis
      by (auto simp add: noDblBk_def tape_of_nat_def tape_of_list_def)
  next
    case (Cons x xs)
    then have "nl = x # xs" .
    show ?thesis
    proof -
      from \<open>nl = x # xs\<close> have "noDblBk (<a # nl>) = noDblBk(<a> @ Bk # <x # xs>)"
        by (auto simp add: tape_of_nat_list_cons_eq)
      also with IV and \<open>nl = x # xs\<close> have "... = True" using noDblBk_cons_cons by auto
      finally show ?thesis by auto
    qed
  qed
qed

lemma hasDblBk_L1: "\<lbrakk> CR = rs @ [Bk] @ Bk # rs'; noDblBk CR \<rbrakk> \<Longrightarrow> False"  
  by (metis  add_diff_cancel_left' append.simps(2)
      append_assoc cell.simps(2) length_Cons length_append
      length_append_singleton noDblBk_def nth_append_length zero_less_Suc zero_less_diff)

lemma hasDblBk_L2: "\<lbrakk> C = Bk # cls; noDblBk C \<rbrakk> \<Longrightarrow> cls = [] \<or> (\<exists>cls'. cls = Oc#cls')"
  by (metis (full_types) append_Cons append_Nil cell.exhaust hasDblBk_L1 neq_Nil_conv)

lemma hasDblBk_L3: "\<lbrakk> noDblBk C ; C = C1 @ (Bk#C2) \<rbrakk> \<Longrightarrow> C2 = [] \<or> (\<exists>C3. C2 = Oc#C3)"
  by (metis (full_types) append_Cons append_Nil cell.exhaust hasDblBk_L1 neq_Nil_conv)


lemma hasDblBk_L4:
  assumes "noDblBk CL"
    and "r = Bk # rs"
    and "r = rev ls1 @ Oc # rss"
    and "CL = ls1 @ ls2"
  shows "ls2 = [] \<or> (\<exists>bs. ls2 = Oc#bs)"
proof -
  from \<open>r = Bk # rs\<close>  have "last ls1 = Bk"
  proof (cases ls1)
    case Nil
    then have "ls1=[]" .
    with \<open>r = rev ls1 @ Oc # rss\<close> have "r = Oc # rss" by auto
    with \<open>r = Bk # rs\<close> have False by auto
    then show ?thesis by auto
  next
    case (Cons b bs)
    then have "ls1 = b#bs" .
    with \<open>r = rev ls1 @ Oc # rss\<close> and \<open>r = Bk # rs\<close> show ?thesis              
      by (metis \<open>r = rev ls1 @ Oc # rss\<close>
          last_appendR last_snoc list.simps(3) rev.simps(2) rev_append rev_rev_ident)
  qed
  show ?thesis
  proof (cases ls2)
    case Nil
    then show ?thesis by auto
  next
    case (Cons b bs)
    then have "ls2 = b # bs" .
    show ?thesis
    proof (cases b)
      case Bk
      then have "b = Bk" .      
      with \<open>ls2 = b # bs\<close> have "ls2 = Bk # bs" by auto
      with \<open>CL = ls1 @ ls2\<close> have "CL = ls1 @ Bk # bs" by auto
      then have "CL = butlast ls1 @ [Bk] @ Bk # ls2"
        by (metis \<open>last ls1 = Bk\<close>  \<open>noDblBk CL\<close> \<open>r = Bk # rs\<close> \<open>r = rev ls1 @ Oc # rss\<close>
            append_butlast_last_id append_eq_append_conv2 append_self_conv2
            cell.distinct(1) hasDblBk_L1 list.inject rev_is_Nil_conv)
      with \<open>noDblBk CL\<close> have False
        using hasDblBk_L1 by blast
      then show ?thesis by auto
    next
      case Oc
      with \<open>ls2 = b # bs\<close> show ?thesis by auto
    qed
  qed
qed

lemma hasDblBk_L5:
  assumes "noDblBk CL"
    and "r = Bk # rs"
    and "r = rev ls1 @ Oc # rss"
    and  "CL = ls1 @ [Bk]"
  shows False
  using  assms hasDblBk_L4
  by blast

lemma noDblBk_cases:
  assumes "noDblBk C"
      and "C = C1 @ C2"
      and "C2 = []   \<Longrightarrow> P"
      and "C2 = [Bk] \<Longrightarrow> P"
      and "\<And>C3. C2 = Bk#Oc#C3 \<Longrightarrow> P"
      and "\<And>C3. C2 = Oc#C3 \<Longrightarrow> P"
  shows "P"
proof -
  have "C2 = [] \<or> C2 = [Bk] \<or> (\<exists>C3. C2 = Bk#Oc#C3 \<or> C2 = Bk#Bk#C3 \<or> C2 = Oc#C3)"   
    by (metis (full_types) cell.exhaust list.exhaust)
  then show ?thesis    
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) hasDblBk_L3 list.distinct(1) by blast
qed

subsection \<open>Unique decomposition of tapes containing lists of numerals\<close>

text \<open>A lemma about appending lists of numerals.\<close>

lemma append_numeral_list: "\<lbrakk> (nl1::nat list) \<noteq> []; nl2 \<noteq> [] \<rbrakk> \<Longrightarrow> <nl1 @ nl2> = <nl1>@[Bk]@<nl2>"
proof (induct nl1 arbitrary: nl2)
  case Nil
  then show ?case
    by blast
next
  fix a::nat
  fix nl1::"nat list"
  fix nl2::"nat list"
  assume IH: "\<And>nl2. \<lbrakk>nl1 \<noteq> []; nl2 \<noteq> []\<rbrakk> \<Longrightarrow> <nl1 @ nl2> = <nl1> @ [Bk] @ <nl2>"
    and minor1: "a # nl1 \<noteq> []"
    and minor2: "nl2 \<noteq> []"
  show "<(a # nl1) @ nl2> = <a # nl1> @ [Bk] @ <nl2>"
  proof (cases nl1)
    assume "nl1 = []"
    then show "<(a # nl1) @ nl2> = <a # nl1> @ [Bk] @ <nl2>"      
      by (metis append_Cons append_Nil minor2 tape_of_list_def tape_of_nat_list.simps(2) tape_of_nat_list_cons_eq)
  next
    fix na nl1s
    assume "nl1 = na # nl1s"
    then have "nl1 \<noteq> []" by auto
    have "<(a # nl1) @ nl2> = <a # (nl1 @ nl2)>" by auto
    also with \<open>nl1 \<noteq> []\<close> and \<open>nl1 = na # nl1s\<close>
    have "... = <a>@[Bk]@<(nl1 @ nl2)>"
      by (simp add:  tape_of_nat_list_cons_eq)
    also with  \<open>nl1 \<noteq> []\<close> and minor2 and IH
    have "... = <a>@[Bk]@ <nl1> @ [Bk] @ <nl2>" by auto
    finally have "<(a # nl1) @ nl2> = <a>@[Bk]@ <nl1> @ [Bk] @ <nl2>" by auto

    moreover with \<open>nl1 \<noteq> []\<close> and minor2 have "<a # nl1> @ [Bk] @ <nl2> = <a>@[Bk]@ <nl1> @ [Bk] @ <nl2>"
      by (simp add: tape_of_nat_list_cons_eq)
    ultimately 
    show "<(a # nl1) @ nl2> = <a # nl1> @ [Bk] @ <nl2>"
      by auto
  qed
qed

text \<open>A lemma about reverting lists of numerals.\<close>

lemma rev_numeral_list: "rev(<nl::nat list>) = <(rev nl)>"
proof (induct nl)
  case Nil
  then show ?case
    by (simp)
next
  fix a::nat
  fix nl::"nat list"
  assume IH: "rev (<nl>) = <rev nl>"
  show "rev (<a # nl>) = <rev (a # nl)>"
  proof (rule tape_of_nat_list.cases[of nl])
    assume "nl = []"
    then have "rev (<a # nl>) = rev (<a>)"
      by (simp add: tape_of_list_def )
    with \<open>nl = []\<close> show ?thesis
      by (simp add: rev_numeral tape_of_list_def )
  next
    fix n
    assume "nl = [n]"
    then have "rev (<a # nl>) = rev (<a#[n]>)" by auto
    also have "... = rev (<a>@[Bk]@<nl>)"
      by (simp add: \<open>nl = [n]\<close> tape_of_list_def  tape_of_nat_list_cons_eq)
    also have "... = rev(<nl>)@[Bk]@rev(<a>)"
      by simp
    also with IH have "... = <rev nl>@[Bk]@rev(<a>)" by auto
    also with  IH \<open>nl = [n]\<close> have "... = <rev (a # nl)>"
      by (simp add: Cons_eq_append_conv hd_rev rev_numeral tape_of_list_def   )
    finally show "rev (<a # nl>) = <rev (a # nl)>" by auto
  next
    fix n v va
    assume "nl = n # v # va"
    then have "rev (<a # nl>) = rev (<a#n # v # va>)" by auto
    also with \<open>nl = n # v # va\<close> have "... = rev(<nl>)@[Bk]@rev(<a>)"
      by (simp add: tape_of_list_def )
    also with IH have "... = <rev nl>@[Bk]@rev(<a>)" by auto
    finally have "rev (<a # nl>) = <rev nl>@[Bk]@rev(<a>)" by auto

    moreover have "<rev (a # nl)> = <rev nl>@[Bk]@rev(<a>)"
    proof -
      have "<rev (a # nl)> = <rev nl @ [a]>" by auto
      also 
      from \<open>nl = n # v # va\<close> have " <rev nl @ [a]> = <rev nl>@[Bk]@rev(<a>)"
        by (metis  list.simps(3) append_numeral_list rev_is_Nil_conv rev_numeral tape_of_list_def tape_of_nat_list.simps(2))
      finally show "<rev (a # nl)> = <rev nl>@[Bk]@rev(<a>)" by auto
    qed
    ultimately show ?thesis by auto
  qed
qed


text \<open>Some more lemmas about unique decomposition of tapes that contain lists of numerals.\<close>

lemma unique_Bk_postfix_numeral_list_Nil: "<[]> @ Bk \<up> l1 = <yl::nat list> @ Bk \<up> l2 \<Longrightarrow> [] = yl"
proof (induct yl arbitrary: l1  l2)
  case Nil
  then show ?case by auto
next
  fix a
  fix yl:: "nat list"
  fix l1 l2
  assume IV: "\<And>l1 l2. <[]> @ Bk \<up> l1 = <yl> @ Bk \<up> l2 \<Longrightarrow> [] = yl"
  and major: "<[]> @ Bk \<up> l1 = <a # yl> @ Bk \<up> l2"
  then show "[] = a # yl"
    by (metis append.assoc append.simps(1) append.simps(2) cell.distinct(1) list.sel(1) list.simps(3)
        replicate_Suc replicate_app_Cons_same tape_of_list_def tape_of_nat_def tape_of_nat_list.elims
        tape_of_nat_list.simps(3) tape_of_nat_list_cases2)
qed

lemma nonempty_list_of_numerals_neq_BKs: "<a# xs::nat list> \<noteq> Bk \<up> l"
  by (metis append_Nil append_Nil2 list.simps(3) replicate_0 tape_of_list_def
            tape_of_list_empty unique_Bk_postfix_numeral_list_Nil)

(* ENHANCE: simplify proof: use cases "a < b \<or> a = b \<or> b < a" only once (earlier in the proof) *)
lemma unique_Bk_postfix_nonempty_numeral_list:
  "\<lbrakk> xl \<noteq> []; yl \<noteq> [];   <xl::nat list> @ Bk \<up> l1 = <yl::nat list>  @ Bk \<up> l2 \<rbrakk> \<Longrightarrow> xl = yl"
proof (induct xl arbitrary: l1 yl l2)
  fix l1 yl l2
  assume "<[]> @ Bk \<up> l1 = <yl::nat list> @ Bk \<up> l2"
  then show "[] = yl"
    using unique_Bk_postfix_numeral_list_Nil by auto
next
  fix a:: nat
  fix xl:: "nat list"
  fix l1
  fix yl:: "nat list"
  fix l2
  assume IV: "\<And>l1 yl l2. \<lbrakk>xl \<noteq> []; yl \<noteq> []; <xl> @ Bk \<up> l1 = <yl> @ Bk \<up> l2\<rbrakk> \<Longrightarrow> xl = yl"
    and minor_xl: "a # xl \<noteq> []"
    and minor_yl: "yl \<noteq> []"
    and major: "<a # xl> @ Bk \<up> l1 = <yl> @ Bk \<up> l2" 
  show "a # xl = yl"
  proof (cases yl)
    case Nil
    then show ?thesis
      by (metis major tape_of_list_empty unique_Bk_postfix_numeral_list_Nil)      
  next
    fix b:: nat
    fix ys:: "nat list"
    assume Ayl: "yl = b # ys"

    have "a # xl = b # ys"
    proof
      show "a = b \<and> xl = ys"
      proof (cases xl)
        case Nil
        then have "xl = []" .
        from major and \<open>yl = b # ys\<close>
        have "<a # xl> @ Bk \<up> l1 = <b # ys> @ Bk \<up> l2" by auto

        with minor_xl and \<open>xl = []\<close> have "<a # xl::nat list> = <a>"
          by (simp add: local.Nil tape_of_list_def)
        with major and Ayl have "<a> @ Bk \<up> l1 = <b # ys> @ Bk \<up> l2" by auto
        show "a = b \<and> xl = ys"
        proof (cases ys)
          case Nil
          then have "ys = []" .
          then have "<b # ys> = <b>"
            by (simp add: local.Nil tape_of_list_def)
          with \<open><a> @ Bk \<up> l1 = <b # ys> @ Bk \<up> l2\<close>
          have "<a> @ Bk \<up> l1 = <b> @ Bk \<up> l2" by auto
          then have "a = b" 
            by (metis append_same_eq inj_tape_of_list unique_Bk_postfix)
          with \<open>xl = []\<close> and \<open>ys = []\<close>
          show ?thesis by auto
        next
          fix c
          fix ys':: "nat list"
          assume "ys = c# ys'"
          then have "<b # ys> = <b> @ Bk # <ys>"
            by (simp add: Ayl tape_of_list_def)

          with \<open><a> @ Bk \<up> l1 = <b # ys> @ Bk \<up> l2\<close>
          have "<a> @ Bk \<up> l1 = <b> @ Bk # <ys> @ Bk \<up> l2"
            by simp

          show "a = b \<and> xl = ys"
          proof (cases l1)
            case 0
            then have "l1 = 0" .
            with \<open><a> @ Bk \<up> l1 = <b> @ Bk # <ys> @ Bk \<up> l2\<close>
            have "<a> = <b> @ Bk # <ys> @ Bk \<up> l2"
              by auto
            then have False
              by (metis "0"   \<open><a> @ Bk \<up> l1 = <b> @ Bk # <ys> @ Bk \<up> l2\<close>
                  cell.distinct(1)  length_Cons length_append length_replicate less_add_same_cancel1
                  nth_append_length nth_replicate  tape_of_nat_def  zero_less_Suc)
            then show ?thesis by auto
          next
            case (Suc l1')
            then have "l1 = Suc l1'" .
            then have "<a> @ Bk \<up> l1 = <a> @ (Bk #Bk \<up> l1')"
              by simp
            then have F1: "(<a> @ Bk \<up> l1)!(Suc a) = Bk"
              by (metis cell.distinct(1) cell.exhaust length_replicate nth_append_length tape_of_nat_def)
            have "a < b \<or> a = b \<or> b < a" by arith (* move upwards in the proof: do cases only once *)
            then show "a = b \<and> xl = ys"
            proof
              assume "a < b"
              with \<open><a> @ Bk \<up> l1 = <b> @ Bk # <ys> @ Bk \<up> l2\<close>
              have "(<b> @ Bk # <ys> @ Bk \<up> l2)!(Suc a) \<noteq> Bk"              
                by (simp add:  hd_of_numeral_is_Oc  nth_append'  tape_of_nat_def)
              with F1 and \<open><a> @ Bk \<up> l1 = <b> @ Bk # <ys> @ Bk \<up> l2\<close> have False
                by (simp add: \<open>(<a> @ Bk \<up> l1) ! Suc a = Bk\<close>)
              then show "a = b \<and> xl = ys"
                by auto
            next
              assume "a = b \<or> b < a"
              then show ?thesis
              proof
                assume "b < a"
                with \<open><a> @ Bk \<up> l1 = <b> @ Bk # <ys> @ Bk \<up> l2\<close>
                have "(<a> @ Bk \<up> l1)!(Suc a) \<noteq> Bk"
                  by (metis Suc_mono cell.distinct(1) length_replicate nth_append'
                            nth_append_length nth_replicate tape_of_nat_def)
                with F1 have False by auto
                then show ?thesis by auto
              next  
                assume "a=b"
                then have False
                  using \<open>xl = []\<close> and \<open>ys = c# ys'\<close> and \<open><a> @ Bk \<up> l1 = <b> @ Bk # <ys> @ Bk \<up> l2\<close>                  
                  using \<open><a> @ Bk \<up> l1 = <a> @ Bk # Bk \<up> l1'\<close> list.distinct(1) list.inject
                    same_append_eq self_append_conv2 tape_of_list_empty unique_Bk_postfix_numeral_list_Nil
                  by fastforce
                then show ?thesis by auto
              qed
            qed
          qed
        qed
      next
        fix a'::nat 
        fix xs:: "nat list"
        assume "xl = a'#xs"

        from major and \<open>yl = b # ys\<close>
        have "<a # xl> @ Bk \<up> l1 = <b # ys> @ Bk \<up> l2" by auto

        from \<open>xl = a'#xs\<close> have "<a # xl::nat list> = <a> @ Bk # <xl>"
          by (simp add: tape_of_list_def)

        with \<open><a # xl> @ Bk \<up> l1 = <b # ys> @ Bk \<up> l2\<close>
        have "(<a> @ Bk # <xl>) @ Bk \<up> l1 = <b # ys> @ Bk \<up> l2" by auto

        then have F2: "<a> @ [Bk] @ (<xl> @ Bk \<up> l1) = <b # ys> @ Bk \<up> l2" by auto

        then have F3: "(<a> @ [Bk] @ (<xl> @ Bk \<up> l1))!(Suc a) = Bk"
          by (metis Ayl append.simps(1) append.simps(2) length_replicate nth_append_length
                    tape_of_nat_def)

        show "a = b \<and> xl = ys"
        proof (cases ys)
          case Nil
          then have "ys = []" .
          then have "<b # ys> = <b>"
            by (simp add: local.Nil tape_of_list_def)

          with F2
          have "<a> @ [Bk] @ (<xl> @ Bk \<up> l1) = <b> @ Bk \<up> l2" by auto

          have "a < b \<or> a = b \<or> b < a" by arith (* move upwards in the proof: do cases only once *)
          then have False
          proof
            assume "a < b"
            then have "(<b> @ Bk \<up> l2)!(Suc a) \<noteq> Bk"              
              by (simp add: \<open>a < b\<close>   nth_append'  tape_of_nat_def)
            with F2 and F3 show False
              using \<open><a> @ [Bk] @ <xl> @ Bk \<up> l1 = <b> @ Bk \<up> l2\<close> by auto
          next
            assume "a = b \<or> b < a"
            then show False
            proof
              assume "b < a"
              show False
              proof (cases l2)
                case 0
                then have "l2 = 0" .
                then have "<b> @ Bk \<up> l2 = <b>" by auto
                with \<open><a> @ [Bk] @ (<xl> @ Bk \<up> l1) = <b> @ Bk \<up> l2\<close>
                have "<a> @ [Bk] @ (<xl> @ Bk \<up> l1) = <b>" by auto

                with \<open>xl = a'#xs\<close> and \<open>b < a\<close>
                have "length (<a>) < length (<a> @ [Bk] @ (<xl> @ Bk \<up> l1))"
                  by (metis  inj_tape_of_list le_add1 length_append less_irrefl
                      nat_less_le nth_append' nth_equalityI)
                with \<open>b < a\<close> have "b < length (<a> @ [Bk] @ (<xl> @ Bk \<up> l1))"                  
                  by (simp add: \<open><a> @ [Bk] @ <xl> @ Bk \<up> l1 = <b>\<close>   tape_of_nat_def)
                with \<open><a> @ [Bk] @ (<xl> @ Bk \<up> l1) = <b>\<close> show False                 
                  using Suc_less_SucD \<open>b < a\<close> \<open>length (<a>) < length (<a> @ [Bk] @ <xl> @ Bk \<up> l1)\<close>
                        length_replicate not_less_iff_gr_or_eq tape_of_nat_def by auto
              next
                fix l2'
                assume "l2 = Suc l2'"
                with \<open><a> @ [Bk] @ (<xl> @ Bk \<up> l1) = <b> @ Bk \<up> l2\<close>
                have "<a> @ [Bk] @ (<xl> @ Bk \<up> l1) = <b> @ [Bk] @ Bk \<up> l2'" by auto

                from \<open>b < a\<close> have "(<b> @ [Bk] @ Bk \<up> l2')!(Suc b) = Bk"
                  by (metis  append_Cons length_replicate nth_append_length tape_of_nat_def)

                moreover from \<open>b < a\<close> have "(<a> @ [Bk] @ (<xl> @ Bk \<up> l1))!(Suc b) \<noteq> Bk"                  
                  by (simp add: Suc_mono  last_of_numeral_is_Oc  nth_append'  tape_of_nat_def)
                ultimately show False
                  using \<open><a> @ [Bk] @ <xl> @ Bk \<up> l1 = <b> @ [Bk] @ Bk \<up> l2'\<close> by auto
              qed
            next
              assume "a=b"
              with \<open><a> @ [Bk] @ (<xl> @ Bk \<up> l1) = <b> @ Bk \<up> l2\<close> and \<open>xl = a'#xs\<close>
              show False               
                by (metis append_Nil append_eq_append_conv2  list.sel(3) list.simps(3)
                    local.Nil same_append_eq  tape_of_list_empty tl_append2 tl_replicate
                    unique_Bk_postfix_numeral_list_Nil)
            qed
          qed
          then show ?thesis by auto
        next
          fix c
          fix ys':: "nat list"
          assume "ys = c# ys'"

          from \<open>ys = c# ys'\<close> have "(<b # ys>) = (<b> @ [Bk] @ <ys>)"           
            by (simp add: Ayl tape_of_list_def )

          with F2 have "<a> @ [Bk] @ (<xl> @ Bk \<up> l1) = <b> @ [Bk] @ <ys> @ Bk \<up> l2" by auto

          have "a < b \<or> a = b \<or> b < a" by arith (* move upwards in the proof: do cases only once *)
          then show "a = b \<and> xl = ys"
          proof
            assume "a < b"
            with \<open>a < b\<close> have "(<b> @ [Bk] @ <ys> @ Bk \<up> l2) !(Suc a) \<noteq> Bk"
              by (simp add: hd_of_numeral_is_Oc  nth_append'  tape_of_nat_def)

            with F3 and \<open><a> @ [Bk] @ (<xl> @ Bk \<up> l1) = <b> @ [Bk] @ <ys> @ Bk \<up> l2\<close>
            have False
              by auto
            then show ?thesis by auto
          next
            assume "a = b \<or> b < a"
            then show ?thesis
            proof
              assume "b < a"

              from \<open>b < a\<close> and \<open><a> @ [Bk] @ (<xl> @ Bk \<up> l1) = <b> @ [Bk] @ <ys> @ Bk \<up> l2\<close>
              have "(<b> @ [Bk] @ <ys> @ Bk \<up> l2) ! Suc b = Bk"                  
                by (metis  append_Cons cell.distinct(1) cell.exhaust length_replicate
                           nth_append_length tape_of_nat_def)

              moreover from \<open>b < a\<close> and \<open><a> @ [Bk] @ (<xl> @ Bk \<up> l1) = <b> @ [Bk] @ <ys> @ Bk \<up> l2\<close>
              have "(<a> @ [Bk] @ (<xl> @ Bk \<up> l1)) ! Suc b \<noteq>  Bk"                
                by (metis Suc_mono cell.distinct(1) length_replicate nth_append' nth_replicate tape_of_nat_def)
              ultimately have False using \<open><a> @ [Bk] @ (<xl> @ Bk \<up> l1) = <b> @ [Bk] @ <ys> @ Bk \<up> l2\<close>                  
                by auto
              then show ?thesis by auto
            next 
              assume "a = b"
              with \<open><a> @ [Bk] @ (<xl> @ Bk \<up> l1) = <b> @ [Bk] @ <ys> @ Bk \<up> l2\<close>
              have "<xl> @ Bk \<up> l1 =  <ys> @ Bk \<up> l2" by auto
              moreover from \<open>xl = a'#xs\<close> have "xl \<noteq> []" by auto
              moreover from \<open>ys = c# ys'\<close> have "ys \<noteq> []" by auto
              ultimately have "xl = ys" using IV by auto
              with \<open>a = b\<close> show ?thesis
                by auto
            qed
          qed
        qed
      qed
    qed
    with \<open>yl = b # ys\<close> show ?thesis by auto
  qed
qed

corollary unique_Bk_postfix_numeral_list: "<xl::nat list> @ Bk \<up> l1 = <yl::nat list> @ Bk \<up> l2 \<Longrightarrow> xl = yl"
  by (metis append_Nil tape_of_list_def tape_of_list_empty
            unique_Bk_postfix_nonempty_numeral_list unique_Bk_postfix_numeral_list_Nil)


text \<open>Some more lemmas about noDblBks in lists of numerals.\<close>

lemma numeral_list_head_is_Oc: "(nl::nat list) \<noteq> [] \<Longrightarrow> hd (<nl>) = Oc"
proof -
  assume A: "(nl::nat list) \<noteq> []"
  then have "(\<exists>r'. <nl> = Oc # r')"
    using append_Nil tape_of_list_empty tape_of_nat_list_cases2 unique_Bk_postfix_numeral_list_Nil by fastforce
  then obtain r' where w_r': "<nl> = Oc # r'" by blast
  then show "hd (<nl>) = Oc" by auto
qed

lemma numeral_list_last_is_Oc: "(nl::nat list) \<noteq> [] \<Longrightarrow> last (<nl>) = Oc"
proof -
  assume A: "(nl::nat list) \<noteq> []"
  then have "<nl> = <rev (rev nl)>" by auto
  also have "... = rev (<rev nl>)" by (auto simp add: rev_numeral_list)
  finally have "<nl> = rev (<rev nl>)" by auto
  moreover from A have "hd (<rev nl>) = Oc" by (auto simp add: numeral_list_head_is_Oc)
  with A have "last (rev (<rev nl>)) = Oc"
    by (simp add: last_rev)
  ultimately show ?thesis
    by (simp add: \<open>last (rev (<rev nl>)) = Oc\<close>)
qed

lemma noDblBk_tape_of_nat_list_imp_noDblBk_tl: "noDblBk (<nl>) \<Longrightarrow> noDblBk (tl (<nl>))"
proof (cases "<nl>")
  case Nil
  then show ?thesis
    by (simp add: local.Nil noDblBk_Nil)
next
  fix a nls
  assume "noDblBk (<nl>)" and "<nl> = a # nls"
  then have "noDblBk (a # nls)" by auto
  then have "\<forall>i. Suc i < length (a # nls) \<and> (a # nls) ! i = Bk \<longrightarrow> (a # nls) ! Suc i = Oc"
    using noDblBk_def by auto
  then have "noDblBk (nls)" using noDblBk_def  by auto
  with \<open><nl> = a # nls\<close> show "noDblBk (tl (<nl>))" using noDblBk_def  by auto
qed

lemma noDblBk_tape_of_nat_list_cons_imp_noDblBk_tl: "noDblBk (a # <nl>) \<Longrightarrow> noDblBk (<nl>)"
proof -
  assume "noDblBk (a # <nl>)"
  then have "\<forall>i. Suc i < length (a # <nl>) \<and> (a # <nl>) ! i = Bk \<longrightarrow> (a # <nl>) ! Suc i = Oc"
    using noDblBk_def by auto
  then show "noDblBk (<nl>)" using   noDblBk_def  by auto
qed

lemma noDblBk_tape_of_nat_list_imp_noDblBk_cons_Bk: "(nl::nat list) \<noteq> [] \<Longrightarrow> noDblBk ([Bk] @ <nl>)"
proof -
  assume "(nl::nat list) \<noteq> []"
  then have major: "<(0::nat) # nl> = <0::nat> @ Bk # <nl>"
    using tape_of_nat_list_cons_eq 
    by auto
  moreover have "noDblBk (<(0::nat) # nl>)" by (rule noDblBk_tape_of_nat_list)
  ultimately have "noDblBk (<0::nat> @ Bk # <nl>)" by auto
  then have "noDblBk (Oc # Bk # <nl>)"
    by (simp add:  cell.exhaust noDblBk_tape_of_nat_list   tape_of_nat_def)
  then show ?thesis 
    using major
    by (metis append_eq_Cons_conv  empty_replicate  list.sel(3) noDblBk_tape_of_nat_list_imp_noDblBk_tl 
        replicate_Suc self_append_conv2 tape_of_nat_def )
qed

end
