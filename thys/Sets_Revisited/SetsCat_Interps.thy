(*  Title:       SetsCat_Interps
    Author:      Eugene W. Stark <stark@cs.stonybrook.edu>, 2026
    Maintainer:  Eugene W. Stark <stark@cs.stonybrook.edu>
*)

chapter "Interpretations of \<open>sets_cat\<close>"

theory SetsCat_Interps
imports Category3.ConcreteCategory Category3.ZFC_SetCat Category3.Colimit
        SetsCat Universe_Interps
begin

  text\<open>
    In this section we construct two interpretations of the @{locale sets_cat} locale:
    one using ``finite'' as the notion of smallness and one that uses \<open>small\<close>
    from the theory \<open>ZFC_in_HOL\<close>.  These interpretations demonstrate
    the consistency of the variants of the @{locale sets_cat} locale: the interpretation
    using finiteness validates the @{locale sets_cat_with_tupling} locale in unextended HOL,
    and the interpretation in terms of \<open>ZFC_in_HOL\<close> validates the
    @{locale sets_cat_with_tupling_and_infinity} locale, assuming that the axiomatization
    of \<open>ZFC_in_HOL\<close> is consistent with HOL.
  \<close>


  section "Category of Finite Sets"

  text\<open>
    The \<open>finite_sets_cat\<close> locale defines a category having as objects the natural numbers
    and as arrows from \<open>m\<close> to \<open>n\<close> the functions from \<open>m\<close>-element sets to \<open>n\<close>-element sets.
    In view of \<open>SetsCat.categoricity\<close>, this is the unique interpretation (up to equivalence
    of categories) of @{locale sets_cat} having a countably infinite collection of arrows.
  \<close>

  locale finite_sets_cat
  begin

    abbreviation OBJ
    where "OBJ \<equiv> UNIV :: nat set"

    abbreviation HOM
    where "HOM \<equiv> \<lambda>m n. {1..m :: nat} \<rightarrow>\<^sub>E {1..n :: nat}"

    abbreviation Id
    where "Id n \<equiv> \<lambda>x :: nat. if x \<in> {1..n} then x else undefined"

    abbreviation Comp
    where "Comp _ _ m \<equiv> compose {1..m}"

    interpretation Fin: concrete_category OBJ HOM Id Comp
      by unfold_locales fastforce+  (* 15 sec *)

    abbreviation comp
    where "comp \<equiv> Fin.COMP"

    lemma terminal_MkIde_1:
    shows "Fin.terminal (Fin.MkIde 1)"
    proof
      show 1: "Fin.ide (Fin.MkIde 1)"
        using Fin.ide_MkIde by blast
      show "\<And>a. Fin.ide a \<Longrightarrow> \<exists>!f. Fin.in_hom f a (Fin.MkIde 1)"
      proof -
        fix a
        assume a: "Fin.ide a"
        let ?Ta = "\<lambda>x. if x \<in> {1..Fin.Dom a} then 1 else undefined"
        have 2: "HOM (Fin.Dom a) 1 = {?Ta}"
          by (cases "Fin.Dom a = 0") auto
        have "Fin.hom a (Fin.MkIde 1) = {Fin.MkArr (Fin.Dom a) 1 ?Ta}"
        proof
          show "{Fin.MkArr (Fin.Dom a) 1 ?Ta} \<subseteq> Fin.hom a (Fin.MkIde 1)"
            using a 1 2 Fin.bij_betw_hom_Hom [of a "Fin.MkIde 1"] by fastforce
          show "Fin.hom a (Fin.MkIde 1) \<subseteq> {Fin.MkArr (Fin.Dom a) 1 ?Ta}"
            using a 1 2 Fin.bij_betw_hom_Hom(1-4) [of a "Fin.MkIde 1"]
            by auto[1] (simp add: Pi_iff)
        qed
        thus "\<exists>!f. Fin.in_hom f a (Fin.MkIde 1)"
          by (metis (no_types, lifting) mem_Collect_eq singleton_iff)
      qed
    qed

    sublocale category_with_terminal_object comp
      using terminal_MkIde_1
      by unfold_locales auto

    notation some_terminal  ("\<one>\<^sup>?")

    sublocale sets_cat_base \<open>finite :: nat set \<Rightarrow> bool\<close> comp
      by (unfold_locales) (meson finite_surj lepoll_iff)

    sublocale small_finite \<open>finite :: nat set \<Rightarrow> bool\<close>
      using Universe_Interps.small_finite_finset by blast

    sublocale small_powerset \<open>finite :: nat set \<Rightarrow> bool\<close>
      using small_powerset_finset by auto

    lemma finite_HOM:
    shows "finite (HOM m n)"
      by (simp add: finite_PiE)

    lemma card_HOM:
    shows "card (HOM m n) = n ^ m"
      by (simp add: card_funcsetE)

    lemma terminal_char\<^sub>F\<^sub>S\<^sub>C:
    shows "Fin.terminal a \<longleftrightarrow> a = Fin.MkIde 1"
    proof
      show "a = Fin.MkIde 1 \<Longrightarrow> Fin.terminal a"
        using terminal_MkIde_1 by blast
      assume a: "Fin.terminal a"
      have "a = Fin.MkIde (Fin.Dom a)"
        using a Fin.terminal_def Fin.MkIde_Dom' by auto
      moreover have "Fin.Dom a = 1"
      proof -
        have "Fin.Dom a \<noteq> 1 \<Longrightarrow> \<not> (\<exists>!f. Fin.in_hom f a (Fin.MkIde 1))"
        proof -
          assume 1: "Fin.Dom a \<noteq> 1"
          have "card (HOM 1 (Fin.Dom a)) \<noteq> 1"
            using 1 card_HOM
            by (metis power_one_right)
          moreover have "card (HOM 1 (Fin.Dom a)) = card (Fin.hom (Fin.MkIde 1) a)"
            by (metis (no_types, lifting) HOL.ext Fin.Dom.simps(1) a Fin.bij_betw_hom_Hom(5)
              bij_betw_same_card terminal_MkIde_1 Fin.terminal_def)
          moreover have "\<And>A. (\<exists>!x. x \<in> A) \<longleftrightarrow> card A = 1"
            by (metis card_1_singletonE ex_in_conv insert_iff is_singletonI' is_singleton_altdef)
          ultimately show "\<not> (\<exists>!f. Fin.in_hom f a (Fin.MkIde 1))"
            by (metis (no_types, lifting) a mem_Collect_eq terminal_MkIde_1 Fin.terminal_def)
        qed
        thus ?thesis
          using a Fin.terminal_def terminal_MkIde_1 by force
      qed
      ultimately show "a = Fin.MkIde 1" by auto
    qed

    lemma MkIde_1_eq:
    shows "Fin.MkIde 1 = \<one>\<^sup>?"
      using terminal_char\<^sub>F\<^sub>S\<^sub>C terminal_some_terminal by presburger

    lemma finite_Set:
    assumes "Fin.ide a"
    shows "finite (Set a)"
      by (metis assms bij_betw_finite Fin.bij_betw_hom_Hom(5) finite_HOM ide_some_terminal)

    lemma card_Set:
    assumes "Fin.ide a"
    shows "card (Set a) = Fin.Dom a"
    proof -
      have "Set a = Fin.hom (Fin.MkIde 1) a"
        using assms MkIde_1_eq by presburger
      moreover have "eqpoll (Fin.hom (Fin.MkIde 1) a) (HOM 1 (Fin.Dom a))"
        using assms Fin.bij_betw_hom_Hom(5)[of "Fin.MkIde 1" a] eqpoll_def
              MkIde_1_eq ide_some_terminal
        by auto
      moreover have "card (HOM 1 (Fin.Dom a)) = Fin.Dom a"
        using card_HOM
        by (metis power_one_right)
      ultimately show ?thesis
        by (metis (lifting) bij_betw_same_card eqpoll_def)
    qed

    abbreviation mkpoint
    where "mkpoint n k \<equiv> Fin.MkArr 1 n (\<lambda>x. if x = 1 then k :: nat else undefined)"

    abbreviation valof
    where "valof x \<equiv> Fin.Map x (1 :: nat)"

    lemma mkpoint_in_hom [intro, simp]:
    assumes "k \<in> {1..n}"
    shows "Fin.in_hom (mkpoint n k) (Fin.MkIde 1) (Fin.MkIde n)"
      using assms Fin.MkArr_in_hom [of 1 n _ "Fin.MkIde 1" "Fin.MkIde n"] by fastforce

    lemma valof_in_range:
    assumes "Fin.in_hom x \<one>\<^sup>? a"
    shows "valof x \<in> {1..Fin.Dom a}"
      using assms Fin.arr_char [of x] Fin.dom_char Fin.cod_char
      by (metis (no_types, lifting) Fin.Dom.simps(1) MkIde_1_eq PiE_E atLeastAtMost_singleton'
        Fin.in_hom_char singletonI)

    lemma valof_mkpoint:
    shows "valof (mkpoint n k) = k"
      by force

    lemma mkpoint_valof:
    assumes "Fin.in_hom x \<one>\<^sup>? a"
    shows "mkpoint (Fin.Dom a) (valof x) = x"
    proof (intro Fin.arr_eqI)
      show "Fin.arr (mkpoint (Fin.Dom a) (valof x))"
        using assms mkpoint_in_hom valof_in_range by blast
      show 1: "Fin.arr x"
        using assms by blast
      show 2: "Fin.Dom (mkpoint (Fin.Dom a) (valof x)) = Fin.Dom x"
        by (metis (lifting) Fin.Dom.simps(1) MkIde_1_eq assms Fin.in_hom_char)
      show "Fin.Cod (mkpoint (Fin.Dom a) (valof x)) = Fin.Cod x"
        by (metis (lifting) Fin.Cod.simps(1) MkIde_1_eq assms Fin.in_hom_char)
      show "Fin.Map (mkpoint (Fin.Dom a) (valof x)) = Fin.Map x"
      proof -
        have "Fin.Map (mkpoint (Fin.Dom a) (valof x)) =
              (\<lambda>k. if k = 1 then valof x else undefined)"
          by simp
        also have "... = Fin.Map x"
        proof
          fix k
          show "(if k = 1 then valof x else undefined) = Fin.Map x k"
            using "1" "2" Fin.arr_char by auto
        qed
        finally show ?thesis by blast
      qed
    qed

    lemma Map_arr_eq:
    assumes "Fin.in_hom f a b"
    shows "Fin.Map f = (\<lambda>k. if k \<in> {1..Fin.Dom a}
                            then Fin.Map (Fun f (mkpoint (Fin.Dom a) k)) 1
                            else undefined)"
      (is "Fin.Map f = ?F")
    proof
      fix k
      show "Fin.Map f k = ?F k"
      proof (cases "k \<in> {1..Fin.Dom a}")
        case False
        show ?thesis using False
          by (metis (no_types, lifting) Fin.Map_in_Hom PiE_arb assms Fin.in_hom_char)
        next
        case True
        have "?F k = Fin.Map (Fun f (mkpoint (Fin.Dom a) k)) 1"
          using True by simp
        also have "... = Fin.Map (comp f (mkpoint (Fin.Dom a) k)) 1"
          using assms True mkpoint_in_hom [of k "Fin.Dom a"] MkIde_1_eq Fin.in_homE
                Fin.in_hom_char Fun_def
          by auto
        also have "... = Fin.Map f (Fin.Map (mkpoint (Fin.Dom a) k) (1 :: nat))"
          using assms True mkpoint_in_hom Fin.in_hom_char Fin.Map_comp by auto
        also have "... = Fin.Map f k"
          by force
        finally show ?thesis by simp
      qed
    qed

    sublocale sets_cat \<open>finite :: nat set \<Rightarrow> bool\<close> comp
    proof
      show "\<And>a. Fin.ide a \<Longrightarrow> nat_tupling.small (Set a)"
        using finite_Set finset_small_iff_finite by blast
      show "\<And>A. \<lbrakk>nat_tupling.small A; A \<subseteq> Collect Fin.arr\<rbrakk> \<Longrightarrow> \<exists>a. Fin.ide a \<and> Set a \<approx> A"
        by (metis (no_types, lifting) Fin.Dom.simps(1) card_Set eqpoll_iff_card finite_Set
            finset_small_iff_finite Fin.ide_MkIde iso_tuple_UNIV_I)
      show "\<And>a b. \<lbrakk>Fin.ide a; Fin.ide b\<rbrakk> \<Longrightarrow> inj_on Fun (Fin.hom a b)"
        using Map_arr_eq Fin.in_hom_char
        by (intro inj_onI Fin.arr_eqI) auto
      show "\<And>a b. \<lbrakk>Fin.ide a; Fin.ide b\<rbrakk> \<Longrightarrow> Hom a b \<subseteq> Fun ` Fin.hom a b"
      proof
        fix a b
        assume a: "Fin.ide a" and b: "Fin.ide b"
        fix F
        assume F: "F \<in> Hom a b"
        show "F \<in> Fun ` Fin.hom a b"
        proof
          let ?F' = "\<lambda>k. if k \<in> {1..Fin.Dom a}
                         then valof (F (mkpoint (Fin.Dom a) k))
                         else undefined"
          let ?f = "Fin.MkArr (Fin.Dom a) (Fin.Dom b) ?F'"
          show f: "?f \<in> Fin.hom a b"
          proof
            show "Fin.in_hom ?f a b"
            proof
              show "Fin.Dom a \<in> UNIV" by auto
              show "Fin.Dom b \<in> UNIV" by auto
              show "a = Fin.MkIde (Fin.Dom a)"
                using a Fin.MkIde_Dom' by presburger
              show "b = Fin.MkIde (Fin.Dom b)"
                using b Fin.MkIde_Dom' by presburger
              show "?F' \<in> HOM (Fin.Dom a) (Fin.Dom b)"
              proof
                fix k
                show "k \<notin> {1..Fin.Dom a} \<Longrightarrow> ?F' k = undefined" by auto
                show "k \<in> {1..Fin.Dom a} \<Longrightarrow> ?F' k \<in> {1..Fin.Dom b}"
                proof -
                  assume k: "k \<in> {1..Fin.Dom a}"
                  have "?F' k = valof (F (mkpoint (Fin.Dom a) k))"
                    using k by simp
                  moreover have "... \<in> {1..Fin.Dom b}"
                  proof -
                    have "F (mkpoint (Fin.Dom a) k) \<in> Fin.hom \<one>\<^sup>? b"
                      using a k F mkpoint_in_hom MkIde_1_eq \<open>a = Fin.MkIde (Fin.Dom a)\<close>
                      by force
                    thus ?thesis
                      using valof_in_range by blast
                  qed
                  ultimately show ?thesis by auto
                qed
              qed
            qed
          qed
          show "F = Fun ?f"
          proof
            fix x
            show "F x = Fun ?f x"
            proof (cases "x \<in> Fin.hom \<one>\<^sup>? a")
              case False
              show ?thesis
                using False F f a Fin.dom_eqI Fin.ide_in_hom Fin.seqI' Fun_def by auto
              next
              case True
              show ?thesis
              proof (intro Fin.arr_eqI)
                show 1: "Fin.arr (F x)"
                  using F True by blast
                show 2: "Fin.arr (Fun ?f x)"
                  using f True a Fin.dom_eqI Fin.ide_in_hom Fin.seqI' Fun_def by auto
                show "Fin.Dom (F x) = Fin.Dom (Fun ?f x)"
                proof -
                  have "Fin.Dom (F x) = Fin.Dom \<one>\<^sup>?"
                    using F True
                    by (metis (no_types, lifting) Int_def Pi_iff Fin.in_hom_char mem_Collect_eq)
                  also have "... = Fin.Dom (Fun ?f x)"
                    using True f
                    by (metis (no_types, lifting) "2" Fin.Dom_comp Fun_def Fin.arrE
                        Fin.in_hom_char mem_Collect_eq Fin.null_char)
                  finally show ?thesis by blast
                qed
                show "Fin.Cod (F x) = Fin.Cod (Fun ?f x)"
                proof -
                  have "Fin.Cod (F x) = Fin.Dom b"
                    using F True
                    by (metis (no_types, lifting) Int_def Pi_mem Fin.in_hom_char mem_Collect_eq)
                  also have "... = Fin.Cod (Fun ?f x)"
                    using True f 2
                    by (metis (no_types, lifting) Fin.Cod.simps(1) Fin.Cod_comp Fin.arrE
                        Fin.null_char Fin.seq_char Fun_def)
                  finally show ?thesis by blast
                qed
                show "Fin.Map (F x) = Fin.Map (Fun ?f x)"
                proof
                  fix k
                  show "Fin.Map (F x) k = Fin.Map (Fun ?f x) k"
                  proof -
                    have "k \<noteq> 1 \<Longrightarrow> ?thesis"
                    proof -
                      assume k: "k \<noteq> 1"
                      have 1: "Fin.Map (F x) k = undefined"
                      proof -
                        have "Fin.in_hom (F x) \<one>\<^sup>? b"
                          using F True by blast
                        thus ?thesis
                          using F True k Map_arr_eq [of "F x" "\<one>\<^sup>?" "b"]
                          by (metis Fin.Dom.simps(1) MkIde_1_eq atLeastAtMost_iff le_antisym)
                      qed
                      also have "... = Fin.Map (Fun ?f x) k"
                      proof -
                        have "Fin.Map (Fun ?f x) k = Fin.Map (comp ?f x) k"
                          using f True Fun_def by fastforce
                        also have "... = compose {1..Fin.Dom x} (Fin.Map ?f) (Fin.Map x) k"
                          using f True Fin.Map_comp
                          by (metis (no_types, lifting) Fin.in_hom_char mem_Collect_eq)
                        also have "... = undefined"
                        proof -
                          have "k \<notin> {1..Fin.Dom x}"
                            using True k
                            by (metis (no_types, lifting) Fin.Dom.simps(1) MkIde_1_eq
                                atLeastAtMost_singleton Fin.in_hom_char mem_Collect_eq
                                singleton_iff)
                          thus ?thesis by auto
                        qed
                        finally show ?thesis by simp
                      qed
                      finally show ?thesis by simp
                    qed
                    moreover have "k = 1 \<Longrightarrow> ?thesis"
                    proof -
                      assume k: "k = 1"
                      have "Fin.Map (Fun ?f x) k = Fin.Map (comp ?f x) k"
                        using "2" Fun_def Fin.arrE Fin.null_char by fastforce
                      also have "... = compose {1..1} (Fin.Map ?f) (Fin.Map x) k"
                        using f True Fin.Map_comp
                        by (metis (lifting) Fin.Dom.simps(1) IntI Int_Collect MkIde_1_eq
                            Fin.in_hom_char)
                      also have "... = ?F' (Fin.Map x k)"
                        apply auto[1]
                        by (auto simp add: k)
                      also have "... = valof (F (mkpoint (Fin.Dom a) (Fin.Map x k)))"
                        using F True k a valof_in_range by auto
                      also have "... = valof (F x)"
                        using F True k mkpoint_valof by force
                      also have "... = Fin.Map (F x) k"
                        using F True k by argo
                      finally show ?thesis by simp
                    qed
                    ultimately show ?thesis by blast
                  qed
                qed
              qed
            qed
          qed
        qed
      qed
    qed

    lemma is_sets_cat:
    shows "sets_cat (finite :: nat set \<Rightarrow> bool) comp"
      ..

    sublocale small_product \<open>finite :: nat set \<Rightarrow> bool\<close>
      using small_product_finset by blast

    sublocale sets_cat_with_pairing \<open>finite :: nat set \<Rightarrow> bool\<close> comp
    proof
      show "\<exists>\<iota>. is_embedding_of \<iota> (Collect Fin.arr \<times> Collect Fin.arr)"
      proof -
        have "\<And>A. \<lbrakk>countable A; infinite A\<rbrakk> \<Longrightarrow> \<exists>\<iota>. \<iota> ` (A \<times> A) \<subseteq> A \<and> inj_on \<iota> (A \<times> A)"
        proof -
          fix A :: "'a set"
          assume countable: "countable A" and infinite: "infinite A"
          obtain \<rho> where \<rho>: "bij_betw \<rho> (A \<times> A) (UNIV :: nat set)"
            using countable infinite countableE_infinite
            by (metis countable_SIGMA infinite_cartesian_product) 
          obtain \<sigma> where \<sigma>: "bij_betw \<sigma> (UNIV :: nat set) A"
            using countable infinite bij_betw_from_nat_into by blast
          have "(\<sigma> \<circ> \<rho>) ` (A \<times> A) \<subseteq> A \<and> inj_on (\<sigma> \<circ> \<rho>) (A \<times> A)"
            using \<rho> \<sigma>
            by (metis bij_betw_def comp_inj_on_iff equalityD2 image_comp)
          thus "\<exists>\<iota>. \<iota> ` (A \<times> A) \<subseteq> A \<and> inj_on \<iota> (A \<times> A)" by blast
        qed
        moreover have "countable (Collect Fin.arr) \<and> infinite (Collect Fin.arr)"
        proof
          show "countable (Collect Fin.arr)"
          proof -
            have "Collect Fin.arr =
                  (\<Union>ab\<in>Collect Fin.ide \<times> Collect Fin.ide. Fin.hom (fst ab) (snd ab))"
            proof
              show "(\<Union>ab\<in>Collect Fin.ide \<times> Collect Fin.ide. Fin.hom (fst ab) (snd ab)) \<subseteq>
                    Collect Fin.arr"
                by blast
              show "Collect Fin.arr \<subseteq>
                    (\<Union>ab\<in>Collect Fin.ide \<times> Collect Fin.ide. Fin.hom (fst ab) (snd ab))"
              proof
                fix f
                assume f: "f \<in> Collect Fin.arr"
                have "Fin.ide (Fin.dom f) \<and> Fin.ide (Fin.cod f) \<and>
                      f \<in> Fin.hom (Fin.dom f) (Fin.cod f)"
                  using f Fin.ide_dom Fin.ide_cod by blast
                hence "(Fin.dom f, Fin.cod f) \<in> Collect Fin.ide \<times> Collect Fin.ide \<and>
                       f \<in> Fin.hom (fst (Fin.dom f, Fin.cod f)) (snd (Fin.dom f, Fin.cod f))"
                  by auto
                thus "f \<in> (\<Union>ab\<in>Collect Fin.ide \<times> Collect Fin.ide. Fin.hom (fst ab) (snd ab))"
                  by blast
              qed
            qed
            moreover have "countable (Collect Fin.ide \<times> Collect Fin.ide)"
              using Fin.bij_betw_ide_Obj(5) by force
            moreover have "\<And>ab. ab \<in> Collect Fin.ide \<times> Collect Fin.ide
                                   \<Longrightarrow> finite (Fin.hom (fst ab) (snd ab)) \<and>
                                       card (Fin.hom (fst ab) (snd ab)) =
                                       Fin.Dom (snd ab) ^ Fin.Dom (fst ab)"
              by (metis bij_betw_finite Fin.bij_betw_hom_Hom(5) bij_betw_same_card card_HOM
                finite_HOM mem_Collect_eq mem_Times_iff)
            ultimately show ?thesis
              using countable_UN countable_finite by (metis (lifting))
          qed
          show "infinite (Collect Fin.arr)"
          proof -
            have "\<And>X. \<forall>n. (\<exists>Y. Y \<subseteq> X \<and> card Y \<ge> n) \<Longrightarrow> infinite X"
              by (metis card_mono not_less_eq_eq)
            moreover have "\<forall>n. (\<exists>ab. ab \<in> Collect Fin.ide \<times> Collect Fin.ide \<and>
                                     card (Fin.hom (fst ab) (snd ab)) \<ge> n)"
              by (metis (no_types, lifting) HOL.ext Fin.Dom.simps(1) SigmaI card_Set
                  fst_conv Fin.ide_MkIde ide_some_terminal iso_tuple_UNIV_I mem_Collect_eq
                order_refl snd_conv)
            ultimately show ?thesis
              by (metis (no_types, lifting) Fin.in_homE mem_Collect_eq subsetI)
          qed
        qed
        ultimately show ?thesis by blast
      qed
    qed

    lemma is_sets_cat_with_pairing:
    shows "sets_cat_with_pairing (finite :: nat set \<Rightarrow> bool) comp"
      ..

    sublocale lifting \<open>Collect Fin.arr\<close>
    proof
      show "embeds ({None} \<union> Some ` Collect Fin.arr)"
      proof -
        have "\<And>n :: nat. Set (Fin.MkIde n) \<subseteq> Collect Fin.arr \<and> card (Set (Fin.MkIde n)) = n"
          using card_Set Fin.ide_MkIde by fastforce
        hence 1: "infinite (Collect Fin.arr)"
          by (metis (lifting) Suc_n_not_le_n card_mono)
        obtain a where a: "a \<in> Collect Fin.arr"
          using 1 not_finite_existsD by auto
        have 2: "eqpoll (Collect Fin.arr) (Collect Fin.arr - {a})"
          using 1 a
          by (metis (lifting) infinite_insert_eqpoll infinite_remove insert_Diff)
        obtain f where f: "f ` Collect Fin.arr \<subseteq> Collect Fin.arr - {a} \<and>
                           inj_on f (Collect Fin.arr)"
          using 2
          by (metis (lifting) bij_betw_def eqpoll_def subset_refl)
        let ?\<iota> = "\<lambda>None \<Rightarrow> a | Some x \<Rightarrow> f x"
        have "is_embedding_of ?\<iota> ({None} \<union> Some ` Collect Fin.arr)"
          using a f by (auto simp add: inj_on_def)
        thus ?thesis by blast
      qed
    qed

    sublocale sets_cat_with_powering \<open>finite :: nat set \<Rightarrow> bool\<close> comp
    proof
      show "embeds {X. X \<subseteq> Collect Fin.arr \<and> nat_tupling.small X}"
      proof -
        have "\<And>X. infinite X \<Longrightarrow> eqpoll (Fpow X) X"
          using Fpow_infinite_bij_betw eqpoll_def by blast
        hence "eqpoll {X. X \<subseteq> Collect Fin.arr \<and> nat_tupling.small X} (Collect Fin.arr)"
          using infinite_univ finset_small_iff_finite Fpow_def
          by (metis (mono_tags, lifting) Collect_cong)
        thus ?thesis
          by (metis (lifting) bij_betw_def eqpoll_def subset_refl)
      qed
    qed

    lemma is_sets_cat_with_powering:
    shows "sets_cat_with_powering (finite :: nat set \<Rightarrow> bool) comp"
      ..

    sublocale small_sum \<open>finite :: nat set \<Rightarrow> bool\<close>
      using small_sum_finset by blast

    sublocale sets_cat_with_tupling \<open>finite :: nat set \<Rightarrow> bool\<close> comp
      by unfold_locales

    theorem is_sets_cat_with_tupling:
    shows "sets_cat_with_tupling (finite :: nat set \<Rightarrow> bool) comp"
      ..

  end

  text\<open>
    Here is the final top-level interpretation.  Note that this is proved in
    ``vanilla HOL'' without any additional axioms.
  \<close>

  interpretation SetsCat\<^sub>f\<^sub>i\<^sub>n: finite_sets_cat .

  section "Category of ZFC Sets"

  text\<open>
    In this section we construct an interpretation of @{locale sets_cat_with_tupling_and_infinity},
    which includes infinite sets.  As this cannot be done in ``vanilla HOL'',
    for this construction we use \<open>ZFC_in_HOL\<close>, which extends HOL with axioms for a type \<open>V\<close>
    that models the set-theoretic universe provided by ZFC.
    Actually, we have previously given, in theory @{theory Category3.ZFC_SetCat},
    a construction of a category of small sets and functions based on \<open>ZFC_in_HOL\<close>.
    Since that work was already done, all we need to do here is to show that
    the previously constructed category interprets the @{locale sets_cat_with_tupling_and_infinity}
    locale.
  \<close>

  locale ZFC_sets_cat
  begin

    text\<open>
      Here we import the previous construction from @{theory Category3.ZFC_SetCat}.
    \<close>

    interpretation ZFC: ZFC_set_cat .

    text\<open>
      We use the notion of ``smallness'' provided by \<open>ZFC_in_HOL\<close>.
    \<close>

    sublocale smallness \<open>ZFC_in_HOL.small :: ZFC_in_HOL.V set \<Rightarrow> bool\<close>
      using lepoll_small by unfold_locales blast

    sublocale sets_cat_base \<open>ZFC_in_HOL.small :: ZFC_in_HOL.V set \<Rightarrow> bool\<close> ZFC.comp
      using ZFC.terminal_unity\<^sub>S\<^sub>C by unfold_locales blast

    sublocale sets_cat \<open>ZFC_in_HOL.small :: ZFC_in_HOL.V set \<Rightarrow> bool\<close> ZFC.comp
    proof
      show "\<And>a. ZFC.ide a \<Longrightarrow> ZFC_universe.small (Set a)"
        unfolding ZFC_universe.small_def
        using ZFC.ide_char\<^sub>S\<^sub>S\<^sub>C ZFC.setp_def ZFC.small_hom
        by (meson eqpoll_sym small_elts small_eqpoll)
      show "\<And>A. \<lbrakk>ZFC_universe.small A; A \<subseteq> Collect ZFC.arr\<rbrakk> \<Longrightarrow> \<exists>a. ZFC.ide a \<and> Set a \<approx> A"
      proof -
        fix A
        assume small: "ZFC_universe.small A" and A: "A \<subseteq> Collect ZFC.arr"
        let ?V = "\<lambda>f. vpair
                        (vpair (ZFC.V_of_ide (ZFC.dom f)) (ZFC.V_of_ide (ZFC.cod f)))
                        (ZFC.V_of_arr f)"
        let ?A' = "ZFC.UP ` ?V ` A"
        have "ZFC.ide (ZFC.mkIde ?A') \<and> ZFC.set (ZFC.mkIde ?A') = ?A'"
          using ZFC.ide_mkIde ZFC.setp_def
          by (metis (lifting) ZFC.set_mkIde bij_betw_imp_surj_on image_mono replacement
              replete_setcat.bij_arr_of small small_iff_ZFC_small
              subset_UNIV)
        moreover have "?A' \<approx> A"
        proof -
          have "inj ZFC.UP"
            by (simp add: ZFC.inj_UP)
          moreover have "inj_on ?V (Collect ZFC.arr)"
          proof (intro inj_onI)
            fix f g
            assume f: "f \<in> Collect ZFC.arr" and g: "g \<in> Collect ZFC.arr"
            assume eq: "?V f = ?V g"
            have "ZFC.V_of_ide (ZFC.dom f) = ZFC.V_of_ide (ZFC.dom g) \<and>
                  ZFC.V_of_ide (ZFC.cod f) = ZFC.V_of_ide (ZFC.cod g) \<and>
                  ZFC.V_of_arr f = ZFC.V_of_arr g"
              using f g eq by fastforce
            thus "f = g"
              by (metis (lifting) ZFC_set_cat.bij_betw_hom_vfun(3) ZFC_set_cat.bij_betw_ide_V(3)
                  ZFC.arr_iff_in_hom f g ZFC.ide_cod ZFC.ide_dom mem_Collect_eq)
          qed
          ultimately show ?thesis
            by (metis (no_types, lifting) A eqpoll_refl inj_on_image_eqpoll_2
                subset_UNIV inj_on_subset)
        qed
        ultimately have "ZFC.ide (ZFC.mkIde ?A') \<and> Set (ZFC.mkIde ?A') \<approx> A"
          by (metis (no_types, lifting) HOL.ext some_terminal_def ZFC.bij_betw_points_and_set
              eqpoll_def ZFC.unity_def eqpoll_trans)
        thus "\<exists>a. ZFC.ide a \<and> Set a \<approx> A" by blast
      qed
      show "\<And>a b. \<lbrakk>ZFC.ide a; ZFC.ide b\<rbrakk> \<Longrightarrow> inj_on Fun (ZFC.hom a b)"
      proof -
        fix a b
        assume a: "ZFC.ide a" and b: "ZFC.ide b"
        show "inj_on Fun (ZFC.hom a b)"
        proof
          fix f g
          assume f: "f \<in> ZFC.hom a b" and g: "g \<in> ZFC.hom a b"
          assume eq: "Fun f = Fun g"
          show "f = g"
          proof (intro ZFC.arr_eqI'\<^sub>S\<^sub>C [of f g])
            show par: "ZFC.par f g"
              using f g by blast
            show "\<And>x. ZFC.in_hom x ZFC.unity (ZFC.dom f) \<Longrightarrow> ZFC.comp f x = ZFC.comp g x"
              by (metis (lifting) some_terminal_def Fun_def par eq mem_Collect_eq ZFC.unity_def)
          qed
        qed
      qed
      show "\<And>a b. \<lbrakk>ZFC.ide a; ZFC.ide b\<rbrakk> \<Longrightarrow> Hom a b \<subseteq> Fun ` ZFC.hom a b"
      proof
        fix a b
        assume a: "ZFC.ide a" and b: "ZFC.ide b"
        fix F
        assume F: "F \<in> Hom a b"
        let ?f = "ZFC.mkArr' a b F"
        have f: "?f \<in> ZFC.hom a b"
          using a b F ZFC.mkArr'_in_hom ZFC.unity_def some_terminal_def by force
        moreover have "Fun ?f = F"
        proof
          fix x
          show "Fun ?f x = F x"
          proof (cases "x \<in> Set a")
            case False
            show ?thesis
            proof -
              have "Fun ?f x = ZFC.null"
                unfolding Fun_def
                using f False ZFC.in_homE by fastforce
              also have "... = F x"
                using False a F by auto
              finally show ?thesis by blast
            qed
            next
            case True
            show ?thesis
            proof -
              have "ZFC.dom ?f = a"
                using f by blast
              thus ?thesis
                unfolding Fun_def
                using a b f F True ZFC.comp_point_mkArr' ZFC.unity_def some_terminal_def
                by force
            qed
          qed
        qed
        ultimately have "\<exists>f. f \<in> ZFC.hom a b \<and> Fun f = F" by blast
        thus "F \<in> Fun ` ZFC.hom a b" by blast
      qed
    qed

    lemma is_sets_cat:
    shows "sets_cat (ZFC_in_HOL.small :: ZFC_in_HOL.V set \<Rightarrow> bool) ZFC.comp"
      ..

    text\<open>
      Arrows of the category can be encoded as elements of \<open>V\<close>.
    \<close>

    abbreviation arr_to_V
    where "arr_to_V f \<equiv> vpair
                          (vpair (ZFC.V_of_ide (ZFC.dom f)) (ZFC.V_of_ide (ZFC.cod f)))
                          (ZFC.V_of_arr f)"

    lemma inj_arr_to_V:
    shows "inj_on arr_to_V (Collect ZFC.arr)"
    proof (intro inj_onI)
      fix f g
      assume f: "f \<in> Collect ZFC.arr" and g: "g \<in> Collect ZFC.arr"
      assume eq: "arr_to_V f = arr_to_V g"
      have "ZFC.V_of_ide (ZFC.dom f) = ZFC.V_of_ide (ZFC.dom g) \<and>
            ZFC.V_of_ide (ZFC.cod f) = ZFC.V_of_ide (ZFC.cod g) \<and>
            ZFC.V_of_arr f = ZFC.V_of_arr g"
        using f g eq by fastforce
      thus "f = g"
        by (metis (lifting) ZFC_set_cat.bij_betw_hom_vfun(3) ZFC_set_cat.bij_betw_ide_V(3)
            ZFC.arr_iff_in_hom f g ZFC.ide_cod ZFC.ide_dom mem_Collect_eq)
    qed

    text\<open>
      As it happens, \<open>V\<close> also embeds into the collection of arrows, so the two are equipollent.
      Thus, the fact that \<open>V\<close> is a universe can be transferred to the collection of arrows.
      So we can save ourselves some work here.
    \<close>

    lemma eqpoll_Collect_arr_V:
    shows "Collect ZFC.arr \<union> {ZFC.null} \<approx> (UNIV :: V set)"
    and "Collect ZFC.arr \<approx> (UNIV :: V set)"
    proof -
      have "inj_on arr_to_V (Collect ZFC.arr)"
        using inj_arr_to_V by blast
      moreover have "ZFC.ide_of_V \<in> UNIV \<rightarrow> Collect ZFC.arr \<and> inj ZFC.ide_of_V"
        by (metis (no_types, lifting) Pi_iff ZFC_set_cat.bij_betw_ide_V(6) bij_betw_def
            ZFC.ide_char imageI mem_Collect_eq)
      ultimately show 1: "Collect ZFC.arr \<approx> (UNIV :: V set)"
        using Schroeder_Bernstein [of arr_to_V "Collect ZFC.arr" UNIV ZFC.ide_of_V ]
        by (simp add: Pi_iff eqpoll_def image_subset_iff)
      moreover have "Collect ZFC.arr \<union> {ZFC.null} \<approx> Collect ZFC.arr"
      proof -
        have "\<And>X a. infinite X \<Longrightarrow> insert a X \<approx> X"
          by (simp add: infinite_insert_eqpoll)
        moreover have "infinite (Collect ZFC.arr)"
        proof -
          have "\<And>X Y. X \<approx> Y \<Longrightarrow> infinite X \<longleftrightarrow> infinite Y"
            using eqpoll_finite_iff by blast
          moreover have "infinite (UNIV :: V set)"
            using infinite_\<omega> rev_finite_subset by blast
          ultimately show ?thesis
            using 1 by blast
        qed
        ultimately show ?thesis by fastforce
      qed
      ultimately show "Collect ZFC.arr \<union> {ZFC.null} \<approx> (UNIV :: V set)"
        using eqpoll_trans by blast
    qed

    sublocale universe \<open>ZFC_in_HOL.small :: ZFC_in_HOL.V set \<Rightarrow> bool\<close> \<open>Collect ZFC.arr\<close> ZFC.null
    proof -
      interpret V: universe \<open>ZFC_in_HOL.small :: ZFC_in_HOL.V set \<Rightarrow> bool\<close> \<open>UNIV :: V set\<close>
        using V_is_universe by blast
      show "universe (ZFC_in_HOL.small :: ZFC_in_HOL.V set \<Rightarrow> bool) (Collect ZFC.arr)"
        using V_is_universe eqpoll_sym V.is_respected_by_equipollence
              eqpoll_Collect_arr_V(2)
        by blast
    qed

    sublocale sets_cat_with_tupling_and_infinity
                \<open>ZFC_in_HOL.small :: ZFC_in_HOL.V set \<Rightarrow> bool\<close> ZFC.comp
      ..

    theorem is_sets_cat_with_tupling_and_infinity:
    shows "sets_cat_with_tupling_and_infinity
             (ZFC_in_HOL.small :: ZFC_in_HOL.V set \<Rightarrow> bool) ZFC.comp"
      ..

  end

  text\<open>
    Here is the final top-level interpretation.
  \<close>

  interpretation SetsCat\<^sub>Z\<^sub>F\<^sub>C: ZFC_sets_cat .

end


