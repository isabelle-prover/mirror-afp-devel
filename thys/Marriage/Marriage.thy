theory Marriage
imports Main 
begin

lemma diff_card_le_card_Diff:
assumes "finite B" shows "card A - card B \<le> card(A - B)"
proof-
  have "card A - card B \<le> card A - card (A \<inter> B)"
    using card_mono[OF assms Int_lower2, of A] by arith
  also have "\<dots> = card(A-B)" using assms by(simp add: card_Diff_subset_Int)
  finally show ?thesis .
qed

theorem marriage: 
  fixes A :: "'a \<Rightarrow> 'b set" and I :: "'a set"
  assumes "finite I" and "\<forall> i\<in>I. finite (A i)"
  shows "(\<exists> R. (\<forall>i\<in>I. R i \<in> A i) \<and> inj_on R I)
  \<longleftrightarrow> (\<forall>J\<subseteq>I. card J \<le> card (\<Union> i\<in>J. A i))" 
  (is "?SDR A I = ?M A I"
   is "(\<exists>R. ?R R A I & ?inj R A I) = _")
proof
  assume "?SDR A I"
  then obtain R where "?R R A I" and "?inj R A I" by auto
  show "?M A I"
  proof clarify
    fix J
    assume "J \<subseteq> I"
    show "card J \<le> card (\<Union>i\<in>J. A i)"
    proof-
      have "inj_on R J" using `?inj R A I` `J\<subseteq>I` by (metis subset_inj_on)
      moreover
      have "(R ` J) \<subseteq> (\<Union>i\<in>J. A i)" using `J\<subseteq>I` `?R R A I` by auto
      moreover
      have "finite (\<Union>i\<in>J. A i)" using `J\<subseteq>I` assms
        by (metis finite_UN_I finite_subset set_mp)
      ultimately show ?thesis by (rule card_inj_on_le)
    qed
  qed
next
  assume "?M A I"
  show "?SDR A I"
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
            assume case1: "\<forall>K\<subset>I. K\<noteq>{} \<longrightarrow> card (\<Union>i\<in>K. A i) \<ge> card K + 1"
            show ?thesis
            proof-
              from `I\<noteq>{}` obtain n where "n\<in>I" by auto
              with `\<forall>i\<in>I. A i \<noteq> {}` have "A n \<noteq> {}" by auto
              then obtain x where "x \<in> A n" by auto
              let ?A' = "\<lambda>i. A i - {x}"
              let ?I' = "I - {n}"
              from `n\<in>I` have "?I' \<subset> I"
                by (metis DiffD2 Diff_subset insertI1 psubset_eq)
              have fin': "\<forall>i\<in>?I'. finite (?A' i)"
                using psubset.prems(1) by auto
              have "?M ?A' ?I'"
              proof clarify
                fix J
                assume "J \<subseteq> ?I'"
                hence "J \<subset> I" by (metis `I - {n} \<subset> I` subset_psubset_trans)
                show "card J \<le> card (\<Union>i\<in>J. ?A' i)"
                proof cases
                  assume "J = {}" thus ?thesis by auto
                next
                  assume "J \<noteq> {}"
                  hence "card J + 1 \<le> card(\<Union>i\<in>J. A i)"
                    using case1 `J\<subset>I` by blast
                  moreover
                  have "card(\<Union>i\<in>J. A i) - 1 \<le> card(\<Union>i\<in>J. ?A' i)" (is "?l \<le> ?r")
                  proof-
                    have "finite J" using `J \<subset> I` psubset(1)
                      by (metis psubset_imp_subset finite_subset)
                    hence 1: "finite(\<Union>i\<in>J. A i)"
                      using `\<forall>i\<in>I. finite(A i)` `J\<subset>I` by force
                    have "?l = card(\<Union>i\<in>J. A i) - card{x}" by simp
                    also have "\<dots> \<le> card((\<Union>i\<in>J. A i) - {x})" using 1
                      by (metis diff_card_le_card_Diff finite.intros)
                    also have "(\<Union>i\<in>J. A i) - {x} = (\<Union>i\<in>J. ?A' i)"
                      by blast
                    finally show ?thesis .
                  qed
                  ultimately show ?thesis by arith
                qed
              qed
              from psubset(2)[OF `?I'\<subset>I` fin' `?M ?A' ?I'`]
              obtain R' where "?R R' ?A' ?I'" "?inj R' ?A' ?I'" by auto
              let ?Rx = "\<lambda>i. if i=n then x else R' i"
              have "?R ?Rx A I" using `x\<in>A n` `?R R' ?A' ?I'` by force
              have "\<forall>i\<in>?I'. ?Rx i \<noteq> x"
                using `?R R' ?A' ?I'` by (metis DiffE insertI1)
              hence "?inj ?Rx A I" using `?inj R' ?A' ?I'`
                by(auto simp: inj_on_def)
              with `?R ?Rx A I` show ?thesis by auto
            qed
          next
            assume "\<not> (\<forall>K\<subset>I. K\<noteq>{} \<longrightarrow> card (\<Union>i\<in>K. A i) \<ge> card K + 1)"
            then obtain K where
              "K\<subset>I" "K\<noteq>{}" and c1: "\<not>(card (\<Union>i\<in>K. A i) \<ge> card K + 1)" by auto
            with psubset.prems(2) have "card (\<Union>i\<in>K. A i) \<ge> card K" by auto
            with c1 have case2: "card (\<Union>i\<in>K. A i)= card K" by auto
            from `K\<subset>I` `finite I` have "finite K" by (auto intro:finite_subset)
            from psubset.prems `K\<subset>I`
            have "\<forall>i\<in>K. finite (A i)" "\<forall>J\<subseteq>K. card J \<le> card(\<Union>i\<in>J. A i)" by auto
            from psubset(2)[OF `K\<subset>I` this]
            obtain R1 where "?R R1 A K" "?inj R1 A K" by auto
            let ?AK = "\<lambda>i. A i - (\<Union>i\<in>K. A i)"
            let ?IK = "I - K"
            from `K\<noteq>{}` `K\<subset>I` have "?IK\<subset>I" by auto
            have "\<forall>i\<in>?IK. finite (?AK i)" using psubset.prems(1) by auto
            have "?M ?AK ?IK"
            proof clarify
              fix J assume "J \<subseteq> ?IK"
              with `finite I` have "finite J" by(auto intro: finite_subset)
              show "card J \<le> card (\<Union>i\<in>J. ?AK i)"
              proof-
                from `J\<subseteq>?IK` have "J \<inter> K = {}" by auto
                have "card J = card(J\<union>K) - card K"
                  using `finite J` `finite K` `J\<inter>K={}`
                  by (auto simp: card_Un_disjoint)
                also have "card(J\<union>K) \<le> card(\<Union>i\<in>J\<union>K. A i)"
                proof -
                  from `J\<subseteq>?IK` `K\<subset>I` have "J \<union> K \<subseteq> I" by auto
                  with psubset.prems(2) show ?thesis by blast
                qed
                also have "\<dots> - card K
                  = card((\<Union>i\<in>J. ?AK i) \<union> (\<Union>i\<in>K. A i)) - card K"
                proof-
                  have "(\<Union>i\<in>J\<union>K. A i) = (\<Union>i\<in>J. ?AK i) \<union> (\<Union>i\<in>K. A i)"
                    using `J\<subseteq>?IK` by auto
                  thus ?thesis by simp
                qed
                also have "\<dots> = card(\<Union>i\<in>J. ?AK i) + card(\<Union>i\<in>K. A i) - card K"
                proof-
                  have "finite (\<Union>i\<in>J. ?AK i)"
                    using `finite J` `J\<subseteq>?IK` psubset(3)
                    by(blast intro: finite_UN_I finite_Diff)
                  moreover have "finite (\<Union>i\<in>K. A i)"
                    using `finite K` `\<forall>i\<in>K. finite (A i)` by auto
                  moreover have "(\<Union>i\<in>J. ?AK i) \<inter> (\<Union>i\<in>K. A i) = {}" by auto
                  ultimately show ?thesis
                    by (simp add: card_Un_disjoint del:Un_Diff_cancel2)
                qed
                also have "\<dots> = card(\<Union>i\<in>J. ?AK i)" using case2 by simp
                finally show ?thesis by simp
              qed
            qed
            from psubset(2)[OF `?IK\<subset>I` `\<forall>i\<in>?IK. finite (?AK i)` `\<forall>J\<subseteq>?IK. card J\<le>card(\<Union>i\<in>J. ?AK i)`]
            obtain R2 where "?R R2 ?AK ?IK" "?inj R2 ?AK ?IK" by auto
            let ?R12 = "\<lambda>i. if i\<in>K then R1 i else R2 i"
            have "\<forall>i\<in>I. ?R12 i \<in> A i" using `?R R1 A K``?R R2 ?AK ?IK` by auto
            moreover have "\<forall>i\<in>I. \<forall>j\<in>I. i\<noteq>j\<longrightarrow>?R12 i \<noteq> ?R12 j"
            proof clarify
              fix i j assume "i\<in>I" "j\<in>I" "i\<noteq>j" "?R12 i = ?R12 j"
              show False
              proof-
                { assume "i\<in>K \<and> j\<in>K \<or> i\<notin>K\<and>j\<notin>K"
                  with `?inj R1 A K` `?inj R2 ?AK ?IK` `?R12 i=?R12 j`
                    `i\<noteq>j` `i\<in>I` `j\<in>I`
                  have ?thesis by (fastsimp simp: inj_on_def)
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
qed

end