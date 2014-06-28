(* Authors: Dongchen Jiang and Tobias Nipkow *)

theory Marriage
imports Main 
begin

theorem marriage_necessary:
  fixes A :: "'a \<Rightarrow> 'b set" and I :: "'a set"
  assumes "finite I" and "\<forall> i\<in>I. finite (A i)"
  and "\<exists>R. (\<forall>i\<in>I. R i \<in> A i) \<and> inj_on R I" (is "\<exists>R. ?R R A & ?inj R A")
  shows "\<forall>J\<subseteq>I. card J \<le> card (UNION J A)"
proof clarify
  fix J
  assume "J \<subseteq> I"
  show "card J \<le> card (UNION J A)"
  proof-
    from assms(3) obtain R where "?R R A" and "?inj R A" by auto
    have "inj_on R J" by(rule subset_inj_on[OF `?inj R A` `J\<subseteq>I`])
    moreover have "(R ` J) \<subseteq> (UNION J A)" using `J\<subseteq>I` `?R R A` by auto
    moreover have "finite (UNION J A)" using `J\<subseteq>I` assms
      by (metis finite_UN_I finite_subset set_mp)
    ultimately show ?thesis by (rule card_inj_on_le)
  qed
qed

text{* The proof by Halmos and Vaughan: *}
theorem marriage_HV:
  fixes A :: "'a \<Rightarrow> 'b set" and I :: "'a set"
  assumes "finite I" and "\<forall> i\<in>I. finite (A i)"
  and "\<forall>J\<subseteq>I. card J \<le> card (UNION J A)" (is "?M A I")
  shows "\<exists>R. (\<forall>i\<in>I. R i \<in> A i) \<and> inj_on R I"
       (is "?SDR A I" is "\<exists>R. ?R R A I & ?inj R A I")
proof-
  { fix I
    have "finite I \<Longrightarrow> \<forall>i\<in>I. finite (A i) \<Longrightarrow> ?M A I \<Longrightarrow> ?SDR A I"
    proof(induct arbitrary: A rule: finite_psubset_induct)
      case (psubset I)
      show ?case
      proof (cases)
        assume "I={}" then show ?thesis by simp
      next 
        assume "I \<noteq> {}"
        have "\<forall>i\<in>I. A i \<noteq> {}"
        proof (rule ccontr)
          assume  "\<not> (\<forall>i\<in>I. A i\<noteq>{})"
          then obtain i where "i\<in>I" "A i = {}" by blast
          hence "{i}\<subseteq> I" by auto
          from mp[OF spec[OF psubset.prems(2)] this] `A i={}`
          show False by simp
        qed
        show ?thesis
        proof cases
          assume case1: "\<forall>K\<subset>I. K\<noteq>{} \<longrightarrow> card (UNION K A) \<ge> card K + 1"
          show ?thesis
          proof-
            from `I\<noteq>{}` obtain n where "n\<in>I" by auto
            with `\<forall>i\<in>I. A i \<noteq> {}` have "A n \<noteq> {}" by auto
            then obtain x where "x \<in> A n" by auto
            let ?A' = "\<lambda>i. A i - {x}" let ?I' = "I - {n}"
            from `n\<in>I` have "?I' \<subset> I"
              by (metis DiffD2 Diff_subset insertI1 psubset_eq)
            have fin': "\<forall>i\<in>?I'. finite (?A' i)" using psubset.prems(1) by auto
            have "?M ?A' ?I'"
            proof clarify
              fix J
              assume "J \<subseteq> ?I'"
              hence "J \<subset> I" by (metis `I - {n} \<subset> I` subset_psubset_trans)
              show "card J \<le> card (UNION J ?A')"
              proof cases
                assume "J = {}" thus ?thesis by auto
              next
                assume "J \<noteq> {}"
                hence "card J + 1 \<le> card(UNION J A)" using case1 `J\<subset>I` by blast
                moreover
                have "card(UNION J A) - 1 \<le> card(UNION J ?A')" (is "?l \<le> ?r")
                proof-
                  have "finite J" using `J \<subset> I` psubset(1)
                    by (metis psubset_imp_subset finite_subset)
                  hence 1: "finite(UNION J A)"
                    using `\<forall>i\<in>I. finite(A i)` `J\<subset>I` by force
                  have "?l = card(UNION J A) - card{x}" by simp
                  also have "\<dots> \<le> card(UNION J A - {x})" using 1
                    by (metis diff_card_le_card_Diff finite.intros)
                  also have "UNION J A - {x} = UNION J ?A'" by blast
                  finally show ?thesis .
                qed
                ultimately show ?thesis by arith
              qed
            qed
            from psubset(2)[OF `?I'\<subset>I` fin' `?M ?A' ?I'`]
            obtain R' where "?R R' ?A' ?I'" "?inj R' ?A' ?I'" by auto
            let ?Rx = "R'(n := x)"
            have "?R ?Rx A I" using `x\<in>A n` `?R R' ?A' ?I'` by force
            have "\<forall>i\<in>?I'. ?Rx i \<noteq> x" using `?R R' ?A' ?I'` by auto
            hence "?inj ?Rx A I" using `?inj R' ?A' ?I'`
              by(auto simp: inj_on_def)
            with `?R ?Rx A I` show ?thesis by auto
          qed
        next
          assume "\<not> (\<forall>K\<subset>I. K\<noteq>{} \<longrightarrow> card (UNION K A) \<ge> card K + 1)"
          then obtain K where
            "K\<subset>I" "K\<noteq>{}" and c1: "\<not>(card (UNION K A) \<ge> card K + 1)" by auto
          with psubset.prems(2) have "card (UNION K A) \<ge> card K" by auto
          with c1 have case2: "card (UNION K A)= card K" by auto
          from `K\<subset>I` `finite I` have "finite K" by (auto intro:finite_subset)
          from psubset.prems `K\<subset>I`
          have "\<forall>i\<in>K. finite (A i)" "\<forall>J\<subseteq>K. card J \<le> card(UNION J A)" by auto
          from psubset(2)[OF `K\<subset>I` this]
          obtain R1 where "?R R1 A K" "?inj R1 A K" by auto
          let ?AK = "\<lambda>i. A i - UNION K A" let ?IK = "I - K"
          from `K\<noteq>{}` `K\<subset>I` have "?IK\<subset>I" by auto
          have "\<forall>i\<in>?IK. finite (?AK i)" using psubset.prems(1) by auto
          have "?M ?AK ?IK"
          proof clarify
            fix J assume "J \<subseteq> ?IK"
            with `finite I` have "finite J" by(auto intro: finite_subset)
            show "card J \<le> card (UNION J ?AK)"
            proof-
              from `J\<subseteq>?IK` have "J \<inter> K = {}" by auto
              have "card J = card(J\<union>K) - card K"
                using `finite J` `finite K` `J\<inter>K={}`
                by (auto simp: card_Un_disjoint)
              also have "card(J\<union>K) \<le> card(UNION (J\<union>K) A)"
              proof -
                from `J\<subseteq>?IK` `K\<subset>I` have "J \<union> K \<subseteq> I" by auto
                with psubset.prems(2) show ?thesis by blast
              qed
              also have "\<dots> - card K = card(UNION J ?AK \<union> UNION K A) - card K"
              proof-
                have "UNION (J\<union>K) A = UNION J ?AK \<union> UNION K A"
                  using `J\<subseteq>?IK` by auto
                thus ?thesis by simp
              qed
              also have "\<dots> = card(UNION J ?AK) + card(UNION K A) - card K"
              proof-
                have "finite (UNION J ?AK)" using `finite J` `J\<subseteq>?IK` psubset(3)
                  by(blast intro: finite_UN_I finite_Diff)
                moreover have "finite (UNION K A)"
                  using `finite K` `\<forall>i\<in>K. finite (A i)` by auto
                moreover have "UNION J ?AK \<inter> UNION K A = {}" by auto
                ultimately show ?thesis
                  by (simp add: card_Un_disjoint del:Un_Diff_cancel2)
              qed
              also have "\<dots> = card(UNION J ?AK)" using case2 by simp
              finally show ?thesis by simp
            qed
          qed
          from psubset(2)[OF `?IK\<subset>I` `\<forall>i\<in>?IK. finite (?AK i)` `\<forall>J\<subseteq>?IK. card J\<le>card(UNION J ?AK)`]
          obtain R2 where "?R R2 ?AK ?IK" "?inj R2 ?AK ?IK" by auto
          let ?R12 = "\<lambda>i. if i\<in>K then R1 i else R2 i"
          have "\<forall>i\<in>I. ?R12 i \<in> A i" using `?R R1 A K``?R R2 ?AK ?IK` by auto
          moreover have "\<forall>i\<in>I. \<forall>j\<in>I. i\<noteq>j\<longrightarrow>?R12 i \<noteq> ?R12 j"
          proof clarify
            fix i j assume "i\<in>I" "j\<in>I" "i\<noteq>j" "?R12 i = ?R12 j"
            show False
            proof-
              { assume "i\<in>K \<and> j\<in>K \<or> i\<notin>K\<and>j\<notin>K"
                with `?inj R1 A K` `?inj R2 ?AK ?IK` `?R12 i=?R12 j` `i\<noteq>j` `i\<in>I` `j\<in>I`
                have ?thesis by (fastforce simp: inj_on_def)
              } moreover
              { assume "i\<in>K \<and> j\<notin>K \<or> i\<notin>K \<and> j\<in>K"
                with `?R R1 A K` `?R R2 ?AK ?IK` `?R12 i=?R12 j` `j\<in>I` `i\<in>I`
                have ?thesis by auto (metis Diff_iff)
              } ultimately show ?thesis by blast
            qed
          qed
          ultimately show ?thesis unfolding inj_on_def by fast
        qed
      qed
    qed
  }
  with assms `?M A I` show ?thesis by auto
qed


text{* The proof by Rado: *}
theorem marriage_Rado:
  fixes A :: "'a \<Rightarrow> 'b set" and I :: "'a set"
  assumes "finite I" and "\<forall> i\<in>I. finite (A i)"
  and "\<forall>J\<subseteq>I. card J \<le> card (UNION J A)" (is "?M A")
  shows "\<exists>R. (\<forall>i\<in>I. R i \<in> A i) \<and> inj_on R I"
       (is "?SDR A" is "\<exists>R. ?R R A & ?inj R A")
proof-
  { have "\<forall>i\<in>I. finite (A i) \<Longrightarrow> ?M A \<Longrightarrow> ?SDR A"
    proof(induct n == "\<Sum>i\<in>I. card(A i) - 1" arbitrary: A)
      case 0
      have "\<forall>i\<in>I.\<exists>a. A(i) = {a}"
      proof (rule ccontr)
        assume  "\<not> (\<forall>i\<in>I.\<exists>a. A i = {a})"
        then obtain i where i: "i:I" "\<forall>a. A i \<noteq> {a}" by blast
        hence "{i}\<subseteq> I" by auto
        from "0"(1-2) mp[OF spec[OF "0.prems"(2)] `{i}\<subseteq>I`] `finite I` i
        show False by (auto simp: card_le_Suc_iff)
      qed
      then obtain R where R: "\<forall>i\<in>I. A i = {R i}" by metis
      then have "\<forall>i\<in>I. R i \<in> A i" by blast
      moreover have "inj_on R I"
      proof (auto simp: inj_on_def)
        fix x y assume "x \<in> I" "y \<in> I" "R x = R y"
        with R spec[OF "0.prems"(2), of "{x,y}"] show "x=y"
          by (simp add:le_Suc_eq card_insert_if split: if_splits)
      qed
      ultimately show ?case by blast
    next
      case (Suc n)
      from Suc.hyps(2)[symmetric, THEN setsum_SucD]
      obtain i where i: "i:I" "2 \<le> card(A i)" by auto
      then obtain x1 x2 where "x1 : A i" "x2 : A i" "x1 \<noteq> x2"
        using Suc(3) by (fastforce simp: card_le_Suc_iff eval_nat_numeral)
      let "?Ai x" = "A i - {x}" let "?A x" = "A(i:=?Ai x)"
      let "?U J" = "UNION J A" let "?Ui J x" = "?U J \<union> ?Ai x"
      have n1: "n = (\<Sum>j\<in>I. card (?A x1 j) - 1)"
        using Suc.hyps(2) Suc.prems(1) i `finite I` `x1:A i`
        by (auto simp: setsum.remove card_Diff_singleton)
      have n2: "n = (\<Sum>j\<in>I. card (?A x2 j) - 1)"
        using Suc.hyps(2) Suc.prems(1) i `finite I` `x2:A i`
        by (auto simp: setsum.remove card_Diff_singleton)
      have finx1: "\<forall>j\<in>I. finite (?A x1 j)" by (simp add: Suc(3))
      have finx2: "\<forall>j\<in>I. finite (?A x2 j)" by (simp add: Suc(3))
      { fix x assume "\<not> ?M (A(i:= ?Ai x))"
        with Suc.prems(2) obtain J
          where J: "J \<subseteq> I" "card J > card(UNION J (A(i:= ?Ai x)))"
          by (auto simp add:not_less_eq_eq Suc_le_eq)
        note fJi = finite_Diff[OF finite_subset[OF `J\<subseteq>I` `finite I`], of "{i}"]
        have fU: "finite(?U (J-{i}))" using `J\<subseteq>I`
          by (metis Diff_iff Suc(3) finite_UN[OF fJi] subsetD)
        have "i \<in> J" using J Suc.prems(2)
          by (simp_all add: UNION_fun_upd not_le[symmetric] del: fun_upd_apply split: if_splits)
        hence "card(J-{i}) \<ge> card(?Ui (J-{i}) x)"
          using fJi J by(simp add: UNION_fun_upd del: fun_upd_apply)
        hence "\<exists>J\<subseteq>I. i \<notin> J \<and> card(J) \<ge> card(?Ui J x) \<and> finite(?U J)"
          by (metis DiffD2 J(1) fU `i \<in> J` insertI1 subset_insertI2 subset_insert_iff)
      } note lem = this
      have "?M (?A x1) \<or> ?M (?A x2)" -- "Rado's Lemma"
      proof(rule ccontr)
        assume "\<not> (?M (?A x1) \<or> ?M (?A x2))"
        with lem obtain J1 J2 where
          J1: "J1\<subseteq>I" "i\<notin>J1" "card J1 \<ge> card(?Ui J1 x1)" "finite(?U J1)" and
          J2: "J2\<subseteq>I" "i\<notin>J2" "card J2 \<ge> card(?Ui J2 x2)" "finite(?U J2)"
          by metis
        note fin1 = finite_subset[OF `J1\<subseteq>I` assms(1)]
        note fin2 = finite_subset[OF `J2\<subseteq>I` assms(1)]
        have finUi1: "finite(?Ui J1 x1)" using Suc(3) by(blast intro: J1(4) i(1))
        have finUi2: "finite(?Ui J2 x2)" using Suc(3) by(blast intro: J2(4) i(1))
        have "card J1 + card J2 + 1 = card(J1 \<union> J2) + 1 + card(J1 \<inter> J2)"
          by simp (metis card_Un_Int fin1 fin2)
        also have "card(J1 \<union> J2) + 1 = card(insert i (J1 \<union> J2))"
          using `i\<notin>J1` `i\<notin>J2` fin1 fin2 by simp
        also have "\<dots> \<le> card(UNION (insert i (J1 \<union> J2)) A)" (is "_ \<le> card ?M")
          by (metis J1(1) J2(1) Suc(4) Un_least i(1) insert_subset)
        also have "?M = ?Ui J1 x1 \<union> ?Ui J2 x2" using `x1\<noteq>x2` by auto
        also have "card(J1 \<inter> J2) \<le> card(UNION (J1 \<inter> J2) A)"
          by (metis J2(1) Suc(4) le_infI2)
        also have "\<dots> \<le> card(?U J1 \<inter> ?U J2)" by(blast intro: card_mono J1(4))
        also have "\<dots> \<le> card(?Ui J1 x1 \<inter> ?Ui J2 x2)"
          using Suc(3) `i\<in>I` by(blast intro: card_mono J1(4))
        finally show False using J1(3) J2(3)
          by(auto simp add: card_Un_Int[symmetric, OF finUi1 finUi2])
      qed
      thus ?case using Suc.hyps(1)[OF n1 finx1] Suc.hyps(1)[OF n2 finx2]
        by (metis DiffD1 fun_upd_def)
    qed
  } with assms `?M A` show ?thesis by auto
qed

end