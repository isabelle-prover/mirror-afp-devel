theory ZFC_SetCat_Interp
imports ZFC_SetCat
begin

  text\<open>
    Here we demonstrate the possibility of making a top-level interpretation of
    the \<open>ZFC_set_cat\<close> locale
\<close>

  interpretation ZFCClsCat: ZFC_class_cat .
  interpretation ZFCSetCat: ZFC_set_cat .

  text\<open>
    To clarify that the category \<open>ZFCSetCat\<close> is what it is supposed to be, we offer the
    following summary results.
  \<close>

  text\<open>
    The set of terminal objects of \<open>ZFCSetCat\<close> is in bijective correspondence with
    the elements of type \<open>V\<close>.
  \<close>

  lemma bij_betw_terminals_and_V:
  shows "bij_betw ZFCSetCat.DN ZFCSetCat.Univ (UNIV :: V set)"
    using ZFCSetCat.bij_DN
    by (metis (no_types, lifting) Collect_cong ZFCSetCat.terminal_char bij_betw_inv_into
        replete_setcat.bij_arr_of)

  text\<open>
    The set of elements of any object of ZFCSetCat is a small subset of the set of
    terminal objects.
  \<close>

  lemma ide_implies_small_set:
  assumes "ZFCSetCat.ide a"
  shows "small (ZFCSetCat.set a)" and "ZFCSetCat.set a \<subseteq> ZFCSetCat.Univ"
    using assms ZFCSetCat.ide_char ZFCSetCat.setp_set_ide ZFCSetCat.setp_def
     apply blast
    using assms ZFCSetCat.setp_imp_subset_Univ ZFCSetCat.setp_set_ide
    by blast

  text\<open>
    Every small set (at an arbitrary type) is in bijective correspondence with the set
    of elements of some object of \<open>ZFCSetCat\<close>.
  \<close>

  lemma small_implies_bij_to_set:
  assumes "small A"
  shows "\<exists>a \<phi>. ZFCSetCat.ide a \<and> bij_betw \<phi> A (ZFCSetCat.set a)"
  proof -
    obtain v \<psi> where v: "bij_betw \<psi> A (ZFC_in_HOL.elts v)"
      by (meson assms bij_betw_the_inv_into eqpoll_def small_eqpoll)
    let ?a = "ZFCSetCat.mkIde (ZFCSetCat.UP ` ZFC_in_HOL.elts v)"
    have a: "ZFCSetCat.ide ?a"
      using ZFCSetCat.setp_def
      by (metis (no_types, lifting) UNIV_I ZFCSetCat.ide_mkIde bij_betw_imp_surj_on
          image_eqI image_subset_iff replacement replete_setcat.bij_arr_of small_elts)
    have "bij_betw (ZFCSetCat.UP \<circ> \<psi>) A (ZFCSetCat.set ?a)"
    proof -
      have "bij_betw ZFCSetCat.UP (ZFC_in_HOL.elts v) (ZFCSetCat.set ?a)"
      proof -
        have "ZFCSetCat.UP ` ZFCSetCat.DN ` (ZFCSetCat.set ?a) = ZFCSetCat.UP ` ZFC_in_HOL.elts v"
          using a ZFCSetCat.set_mkIde ZFCSetCat.DN_UP ZFCSetCat.UP_mapsto ZFCSetCat.setp_def
          by (metis (no_types, lifting) ZFCSetCat.arr_mkIde ZFCSetCat.ideD(1) bij_betw_imp_surj_on
              image_inv_into_cancel replete_setcat.bij_arr_of)
        hence "ZFCSetCat.set ?a = ZFCSetCat.UP ` ZFC_in_HOL.elts v"
          using ZFCSetCat.arr_mkIde ZFCSetCat.ide_char' ZFCSetCat.set_mkIde a
          by presburger
        thus ?thesis
          using ZFCSetCat.inj_UP
                bij_betw_def [of ZFCSetCat.UP "ZFC_in_HOL.elts v" "ZFCSetCat.set ?a"]
          by (simp add: inj_on_def)
      qed
      thus ?thesis
        using bij_betw_trans v by blast
    qed
    thus ?thesis
      using a by blast
  qed

  text\<open>
    For objects \<open>a\<close> and \<open>b\<close> of ZFCSetCat, the arrows from \<open>a\<close> to \<open>b\<close> are in bijective
    correspondence with the extensional functions between the underlying sets of
    terminal objects.
  \<close>

  lemma bij_betw_hom_and_ext_funcset:
  assumes "ZFCSetCat.ide a" and "ZFCSetCat.ide b"
  shows "bij_betw ZFCSetCat.Fun (ZFCSetCat.hom a b) (ZFCSetCat.set a \<rightarrow>\<^sub>E ZFCSetCat.set b)"
  proof (unfold bij_betw_def, intro conjI)
    have 1: "ZFCSetCat.Dom a = ZFCSetCat.set a \<and> ZFCSetCat.Dom b = ZFCSetCat.set b"
      using assms ZFCSetCat.ideD(2) by presburger
    show "inj_on ZFCSetCat.Fun (ZFCSetCat.hom a b)"
      apply (intro inj_onI)
      using ZFCSetCat.arr_eqI\<^sub>S\<^sub>C by blast
    show "ZFCSetCat.Fun ` ZFCSetCat.hom a b = ZFCSetCat.set a \<rightarrow>\<^sub>E ZFCSetCat.set b"
    proof
      show "ZFCSetCat.Fun ` ZFCSetCat.hom a b \<subseteq> ZFCSetCat.set a \<rightarrow>\<^sub>E ZFCSetCat.set b"
      proof -
        have "ZFCSetCat.Fun ` ZFCSetCat.hom a b \<subseteq> ZFCSetCat.Dom a \<rightarrow>\<^sub>E ZFCSetCat.Dom b"
        proof -
          have "\<And>f. f \<in> ZFCSetCat.hom a b \<Longrightarrow>
                       ZFCSetCat.Fun f \<in> ZFCSetCat.Dom a \<rightarrow>\<^sub>E ZFCSetCat.Dom b"
          proof -
            have "\<And>f. f \<in> ZFCSetCat.hom a b \<Longrightarrow>
                        ZFCSetCat.Fun f \<in>
                          extensional (ZFCSetCat.Dom a) \<inter> (ZFCSetCat.Dom a \<rightarrow> ZFCSetCat.Dom b)"
            proof -
              fix f
              assume f: "f \<in> ZFCSetCat.hom a b"
              have "ZFCSetCat.in_hom f a b"
                using f by blast
              thus "ZFCSetCat.Fun f \<in>
                      extensional (ZFCSetCat.Dom a) \<inter> (ZFCSetCat.Dom a \<rightarrow> ZFCSetCat.Dom b)"
                using f 1 Int_iff Pi_iff
                apply (elim ZFCSetCat.in_homE [of f a b])
                using ZFCSetCat.Fun_mapsto [of f] by presburger
            qed
            thus "\<And>f. f \<in> ZFCSetCat.hom a b \<Longrightarrow>
                         ZFCSetCat.Fun f \<in> ZFCSetCat.Dom a \<rightarrow>\<^sub>E ZFCSetCat.Dom b"
              by (simp add: PiE_def)
          qed
          thus ?thesis by blast
        qed
        thus "ZFCSetCat.Fun ` ZFCSetCat.hom a b \<subseteq> ZFCSetCat.set a \<rightarrow>\<^sub>E ZFCSetCat.set b"
          using 1 by blast
      qed
      show "ZFCSetCat.set a \<rightarrow>\<^sub>E ZFCSetCat.set b \<subseteq> ZFCSetCat.Fun ` ZFCSetCat.hom a b"
      proof -
        have "ZFCSetCat.Dom a \<rightarrow>\<^sub>E ZFCSetCat.Dom b \<subseteq> ZFCSetCat.Fun ` ZFCSetCat.hom a b"
        proof
          fix F
          assume F: "F \<in> ZFCSetCat.Dom a \<rightarrow>\<^sub>E ZFCSetCat.Dom b"
          have 2: "\<And>F. F \<in> ZFCSetCat.Dom a \<rightarrow>\<^sub>E ZFCSetCat.Dom b \<Longrightarrow>
                        \<exists>f. ZFCSetCat.in_hom f a b \<and> ZFCSetCat.Fun f = F"
          proof -
            fix F
            have 3: "ZFCSetCat.set a = ZFCSetCat.Dom a \<and> ZFCSetCat.set b = ZFCSetCat.Dom b"
              using assms ZFCSetCat.ideD(2) by presburger
            assume F: "F \<in> ZFCSetCat.Dom a \<rightarrow>\<^sub>E ZFCSetCat.Dom b"
            hence 4: "F \<in> ZFCSetCat.set a \<rightarrow>\<^sub>E ZFCSetCat.set b"
              using 3 by blast
            hence "F \<in> ZFCSetCat.set a \<rightarrow> ZFCSetCat.set b"
              by blast
            hence "\<exists>!f. ZFCSetCat.in_hom f a b \<and> ZFCSetCat.Fun f = restrict F (ZFCSetCat.set a)"
              using assms F ZFCSetCat.fun_complete [of a b] by presburger
            moreover have "restrict F (ZFCSetCat.set a) = F"
              using F 4 PiE_restrict by blast
            ultimately show "\<exists>f. ZFCSetCat.in_hom f a b \<and> ZFCSetCat.Fun f = F"
              by auto
          qed
          obtain f where f: "f \<in> ZFCSetCat.hom a b \<and> ZFCSetCat.Fun f = F"
            using F 2 by blast
          thus "F \<in> ZFCSetCat.Fun ` ZFCSetCat.hom a b"
            by blast
        qed
        thus ?thesis
          using 1 by simp
      qed
    qed
  qed

end
