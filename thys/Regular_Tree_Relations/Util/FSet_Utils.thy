theory FSet_Utils                                      
  imports "HOL-Library.FSet"
    "HOL-Library.List_Lexorder"
    Ground_Terms
begin

context
includes fset.lifting
begin

lift_definition fCollect :: "('a \<Rightarrow> bool) \<Rightarrow> 'a fset" is "\<lambda> P. if finite (Collect P) then Collect P else {}"
  by auto

lift_definition fSigma :: "'a fset \<Rightarrow> ('a \<Rightarrow> 'b fset) \<Rightarrow> ('a \<times> 'b) fset" is Sigma
  by auto

lift_definition is_fempty :: "'a fset \<Rightarrow> bool" is Set.is_empty .
lift_definition fremove :: "'a \<Rightarrow> 'a fset \<Rightarrow> 'a fset" is Set.remove
  by (simp add: remove_def)

lift_definition finj_on :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a fset \<Rightarrow> bool" is inj_on .
lift_definition the_finv_into  :: "'a fset \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a" is the_inv_into .

lemma fCollect_memberI [intro!]:
  "finite (Collect P) \<Longrightarrow> P x \<Longrightarrow> x |\<in>| fCollect P"
  by transfer auto

lemma fCollect_member [iff]:
  "x |\<in>| fCollect P \<longleftrightarrow> finite (Collect P) \<and> P x"
  by transfer (auto split: if_splits)

lemma fCollect_cong: "(\<And>x. P x = Q x) \<Longrightarrow> fCollect P = fCollect Q"
  by presburger
end

syntax
  "_fColl" :: "pttrn \<Rightarrow> bool \<Rightarrow> 'a set"    ("(1{|_./ _|})")
translations
  "{|x. P|}" \<rightleftharpoons> "CONST fCollect (\<lambda>x. P)"

syntax (ASCII)
  "_fCollect" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'a set"  ("(1{(_/|:| _)./ _})")
syntax
  "_fCollect" :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> 'a set"  ("(1{(_/ |\<in>| _)./ _})")
translations
  "{p|:|A. P}" \<rightharpoonup> "CONST fCollect (\<lambda>p. p |\<in>| A \<and> P)"

syntax (ASCII)
  "_fBall"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      ("(3ALL (_/|:|_)./ _)" [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      ("(3EX (_/|:|_)./ _)" [0, 0, 10] 10)

syntax (input)
  "_fBall"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      ("(3! (_/|:|_)./ _)" [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      ("(3? (_/|:|_)./ _)" [0, 0, 10] 10)

syntax
  "_fBall"       :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<forall>(_/|\<in>|_)./ _)" [0, 0, 10] 10)
  "_fBex"        :: "pttrn \<Rightarrow> 'a set \<Rightarrow> bool \<Rightarrow> bool"      ("(3\<exists>(_/|\<in>|_)./ _)" [0, 0, 10] 10)

translations
  "\<forall>x|\<in>|A. P" \<rightleftharpoons> "CONST fBall A (\<lambda>x. P)"
  "\<exists>x|\<in>|A. P" \<rightleftharpoons> "CONST fBex A (\<lambda>x. P)"

syntax (ASCII output)
  "_setlessfAll" :: "[idt, 'a, bool] \<Rightarrow> bool"  ("(3ALL _|<|_./ _)"  [0, 0, 10] 10)
  "_setlessfEx"  :: "[idt, 'a, bool] \<Rightarrow> bool"  ("(3EX _|<|_./ _)"  [0, 0, 10] 10)
  "_setlefAll"   :: "[idt, 'a, bool] \<Rightarrow> bool"  ("(3ALL _|<=|_./ _)" [0, 0, 10] 10)
  "_setlefEx"    :: "[idt, 'a, bool] \<Rightarrow> bool"  ("(3EX _|<=|_./ _)" [0, 0, 10] 10)

syntax
  "_setlessfAll" :: "[idt, 'a, bool] \<Rightarrow> bool"   ("(3\<forall>_|\<subset>|_./ _)"  [0, 0, 10] 10)
  "_setlessfEx"  :: "[idt, 'a, bool] \<Rightarrow> bool"   ("(3\<exists>_|\<subset>|_./ _)"  [0, 0, 10] 10)
  "_setlefAll"   :: "[idt, 'a, bool] \<Rightarrow> bool"   ("(3\<forall>_|\<subseteq>|_./ _)" [0, 0, 10] 10)
  "_setlefEx"    :: "[idt, 'a, bool] \<Rightarrow> bool"   ("(3\<exists>_|\<subseteq>|_./ _)" [0, 0, 10] 10)

translations
 "\<forall>A|\<subset>|B. P" \<rightharpoonup> "\<forall>A. A |\<subset>| B \<longrightarrow> P"
 "\<exists>A|\<subset>|B. P" \<rightharpoonup> "\<exists>A. A |\<subset>| B \<and> P"
 "\<forall>A|\<subseteq>|B. P" \<rightharpoonup> "\<forall>A. A |\<subseteq>| B \<longrightarrow> P"
 "\<exists>A|\<subseteq>|B. P" \<rightharpoonup> "\<exists>A. A |\<subseteq>| B \<and> P"

syntax
  "_fSetcompr" :: "'a \<Rightarrow> idts \<Rightarrow> bool \<Rightarrow> 'a fset"    ("(1{|_ |/_./ _|})")

parse_translation \<open>
  let
    val ex_tr = snd (Syntax_Trans.mk_binder_tr ("EX ", \<^const_syntax>\<open>Ex\<close>));

    fun nvars (Const (\<^syntax_const>\<open>_idts\<close>, _) $ _ $ idts) = nvars idts + 1
      | nvars _ = 1;

    fun setcompr_tr ctxt [e, idts, b] =
      let
        val eq = Syntax.const \<^const_syntax>\<open>HOL.eq\<close> $ Bound (nvars idts) $ e;
        val P = Syntax.const \<^const_syntax>\<open>HOL.conj\<close> $ eq $ b;
        val exP = ex_tr ctxt [idts, P];
      in Syntax.const \<^const_syntax>\<open>fCollect\<close> $ absdummy dummyT exP end;

  in [(\<^syntax_const>\<open>_fSetcompr\<close>, setcompr_tr)] end
\<close>

print_translation \<open>
 [Syntax_Trans.preserve_binder_abs2_tr' \<^const_syntax>\<open>fBall\<close> \<^syntax_const>\<open>_fBall\<close>,
  Syntax_Trans.preserve_binder_abs2_tr' \<^const_syntax>\<open>fBex\<close> \<^syntax_const>\<open>_fBex\<close>]
\<close> \<comment> \<open>to avoid eta-contraction of body\<close>

print_translation \<open>
let
  val ex_tr' = snd (Syntax_Trans.mk_binder_tr' (\<^const_syntax>\<open>Ex\<close>, "DUMMY"));

  fun setcompr_tr' ctxt [Abs (abs as (_, _, P))] =
    let
      fun check (Const (\<^const_syntax>\<open>Ex\<close>, _) $ Abs (_, _, P), n) = check (P, n + 1)
        | check (Const (\<^const_syntax>\<open>HOL.conj\<close>, _) $
              (Const (\<^const_syntax>\<open>HOL.eq\<close>, _) $ Bound m $ e) $ P, n) =
            n > 0 andalso m = n andalso not (loose_bvar1 (P, n)) andalso
            subset (=) (0 upto (n - 1), add_loose_bnos (e, 0, []))
        | check _ = false;

        fun tr' (_ $ abs) =
          let val _ $ idts $ (_ $ (_ $ _ $ e) $ Q) = ex_tr' ctxt [abs]
          in Syntax.const \<^syntax_const>\<open>_fSetcompr\<close> $ e $ idts $ Q end;
    in
      if check (P, 0) then tr' P
      else
        let
          val (x as _ $ Free(xN, _), t) = Syntax_Trans.atomic_abs_tr' abs;
          val M = Syntax.const \<^syntax_const>\<open>_fColl\<close> $ x $ t;
        in
          case t of
            Const (\<^const_syntax>\<open>HOL.conj\<close>, _) $
              (Const (\<^const_syntax>\<open>fmember\<close>, _) $
                (Const (\<^syntax_const>\<open>_bound\<close>, _) $ Free (yN, _)) $ A) $ P =>
            if xN = yN then Syntax.const \<^syntax_const>\<open>_fCollect\<close> $ x $ A $ P else M
          | _ => M
        end
    end;
  in [(\<^const_syntax>\<open>fCollect\<close>, setcompr_tr')] end
\<close>

syntax
  "_fSigma" :: "pttrn \<Rightarrow> 'a fset \<Rightarrow> 'b fset \<Rightarrow> ('a \<times> 'b) set"  ("(3fSIGMA _|:|_./ _)" [0, 0, 10] 10)
translations
  "fSIGMA x|:|A. B" \<rightleftharpoons> "CONST fSigma A (\<lambda>x. B)"

notation
  ffUnion ("|\<Union>|")

context
includes fset.lifting
begin

lemma right_total_cr_fset [transfer_rule]:
  "right_total cr_fset"
  by (auto simp: cr_fset_def right_total_def)

lemma bi_unique_cr_fset [transfer_rule]:
  "bi_unique cr_fset"
  by (auto simp: bi_unique_def cr_fset_def fset_inject)

lemma right_total_pcr_fset_eq [transfer_rule]:
  "right_total (pcr_fset (=))"
  by (simp add: right_total_cr_fset fset.pcr_cr_eq)

lemma bi_unique_pcr_fset [transfer_rule]:
  "bi_unique (pcr_fset (=))"
  by (simp add: fset.pcr_cr_eq bi_unique_cr_fset)


lemma set_fset_of_list_transfer [transfer_rule]:
  "rel_fun (list_all2 A) (pcr_fset A) set fset_of_list"
  unfolding pcr_fset_def rel_set_def rel_fun_def
  by (force simp: list_all2_conv_all_nth in_set_conv_nth cr_fset_def fset_of_list.rep_eq relcompp_apply)
  

lemma fCollectD: "a |\<in>| {|x . P x|} \<Longrightarrow> P a"
  by transfer (auto split: if_splits)

lemma fCollectI: "P a \<Longrightarrow> finite (Collect P) \<Longrightarrow> a |\<in>| {| x. P x|}"
  by (auto intro: fCollect_memberI)

lemma fCollect_fempty_eq [simp]: "fCollect P = {||} \<longleftrightarrow> (\<forall>x. \<not> P x) \<or> infinite (Collect P)"
  by auto

lemma fempty_fCollect_eq [simp]: "{||} = fCollect P \<longleftrightarrow> (\<forall>x. \<not> P x) \<or> infinite (Collect P)"
  by auto


lemma fset_image_conv:
  "{f x | x. x |\<in>| T} = fset (f |`| T)"
  by transfer auto

lemma fimage_def:
  "f |`| A = {| y. \<exists>x|\<in>|A. y = f x |}"
  by transfer auto

lemma ffilter_simp: "ffilter P A = {a |\<in>| A. P a}"
  by transfer auto

lemmas fset_list_fsubset_eq_nth_conv = set_list_subset_eq_nth_conv[Transfer.transferred]
lemmas mem_idx_fset_sound = mem_idx_sound[Transfer.transferred]
\<comment> \<open>Dealing with fset products\<close>

abbreviation fTimes :: "'a fset \<Rightarrow> 'b fset \<Rightarrow> ('a \<times> 'b) fset"  (infixr "|\<times>|" 80)
  where "A |\<times>| B \<equiv> fSigma A (\<lambda>_. B)"

lemma fSigma_repeq:
  "fset (A |\<times>| B) = fset A \<times> fset B"
  by (transfer) auto

lemmas fSigmaI [intro!] = SigmaI[Transfer.transferred]
lemmas fSigmaE [elim!] = SigmaE[Transfer.transferred]
lemmas fSigmaD1 = SigmaD1[Transfer.transferred]
lemmas fSigmaD2 = SigmaD2[Transfer.transferred]
lemmas fSigmaE2 = SigmaE2[Transfer.transferred]
lemmas fSigma_cong = Sigma_cong[Transfer.transferred]
lemmas fSigma_mono = Sigma_mono[Transfer.transferred]
lemmas fSigma_empty1 [simp] = Sigma_empty1[Transfer.transferred]
lemmas fSigma_empty2 [simp] = Sigma_empty2[Transfer.transferred]
lemmas fmem_Sigma_iff [iff] = mem_Sigma_iff[Transfer.transferred]
lemmas fmem_Times_iff = mem_Times_iff[Transfer.transferred]
lemmas fSigma_empty_iff = Sigma_empty_iff[Transfer.transferred]
lemmas fTimes_subset_cancel2 = Times_subset_cancel2[Transfer.transferred]
lemmas fTimes_eq_cancel2 = Times_eq_cancel2[Transfer.transferred]
lemmas fUN_Times_distrib = UN_Times_distrib[Transfer.transferred]
lemmas fsplit_paired_Ball_Sigma [simp, no_atp] = split_paired_Ball_Sigma[Transfer.transferred]
lemmas fsplit_paired_Bex_Sigma [simp, no_atp] = split_paired_Bex_Sigma[Transfer.transferred]
lemmas fSigma_Un_distrib1 = Sigma_Un_distrib1[Transfer.transferred]
lemmas fSigma_Un_distrib2 = Sigma_Un_distrib2[Transfer.transferred]
lemmas fSigma_Int_distrib1 = Sigma_Int_distrib1[Transfer.transferred]
lemmas fSigma_Int_distrib2 = Sigma_Int_distrib2[Transfer.transferred]
lemmas fSigma_Diff_distrib1 = Sigma_Diff_distrib1[Transfer.transferred]
lemmas fSigma_Diff_distrib2 = Sigma_Diff_distrib2[Transfer.transferred]
lemmas fSigma_Union = Sigma_Union[Transfer.transferred]
lemmas fTimes_Un_distrib1 = Times_Un_distrib1[Transfer.transferred]
lemmas fTimes_Int_distrib1 = Times_Int_distrib1[Transfer.transferred]
lemmas fTimes_Diff_distrib1 = Times_Diff_distrib1[Transfer.transferred]
lemmas fTimes_empty [simp] = Times_empty[Transfer.transferred]
lemmas ftimes_subset_iff = times_subset_iff[Transfer.transferred]
lemmas ftimes_eq_iff = times_eq_iff[Transfer.transferred]
lemmas ffst_image_times [simp] = fst_image_times[Transfer.transferred]
lemmas fsnd_image_times [simp] = snd_image_times[Transfer.transferred]
lemmas fsnd_image_Sigma = snd_image_Sigma[Transfer.transferred]
lemmas finsert_Times_insert = insert_Times_insert[Transfer.transferred]
lemmas fTimes_Int_Times = Times_Int_Times[Transfer.transferred]
lemmas fimage_paired_Times = image_paired_Times[Transfer.transferred]
lemmas fproduct_swap = product_swap[Transfer.transferred]
lemmas fswap_product = swap_product[Transfer.transferred]
lemmas fsubset_fst_snd = subset_fst_snd[Transfer.transferred]
lemmas map_prod_ftimes = map_prod_times[Transfer.transferred]


lemma fCollect_case_prod [simp]:
  "{|(a, b). P a \<and> Q b|} = fCollect P |\<times>| fCollect Q"
  by transfer (auto dest: finite_cartesian_productD1 finite_cartesian_productD2)
lemma fCollect_case_prodD:
  "x |\<in>| {|(x, y). A x y|} \<Longrightarrow> A (fst x) (snd x)"
  by auto


(*FIX *)
lemmas fCollect_case_prod_Sigma = Collect_case_prod_Sigma[Transfer.transferred]
lemmas ffst_image_Sigma = fst_image_Sigma[Transfer.transferred]
lemmas fimage_split_eq_Sigma = image_split_eq_Sigma[Transfer.transferred]


\<comment> \<open>Dealing with transitive closure\<close>

lift_definition ftrancl :: "('a \<times> 'a) fset \<Rightarrow> ('a \<times> 'a) fset"  ("(_|\<^sup>+|)" [1000] 999) is trancl
  by auto

lemmas fr_into_trancl [intro, Pure.intro] = r_into_trancl[Transfer.transferred]
lemmas ftrancl_into_trancl [Pure.intro] = trancl_into_trancl[Transfer.transferred]
lemmas ftrancl_induct[consumes 1, case_names Base Step] = trancl.induct[Transfer.transferred]
lemmas ftrancl_mono = trancl_mono[Transfer.transferred]
lemmas ftrancl_trans[trans] = trancl_trans[Transfer.transferred]
lemmas ftrancl_empty [simp] = trancl_empty [Transfer.transferred]
lemmas ftranclE[cases set: ftrancl] = tranclE[Transfer.transferred]
lemmas converse_ftrancl_induct[consumes 1, case_names Base Step] = converse_trancl_induct[Transfer.transferred]
lemmas converse_ftranclE = converse_tranclE[Transfer.transferred]
lemma in_ftrancl_UnI:
  "x |\<in>| R|\<^sup>+| \<or> x |\<in>| S|\<^sup>+| \<Longrightarrow> x |\<in>| (R |\<union>| S)|\<^sup>+|"
  by transfer (auto simp add: trancl_mono)

lemma ftranclD:
  "(x, y) |\<in>| R|\<^sup>+| \<Longrightarrow> \<exists>z. (x, z) |\<in>| R \<and> (z = y \<or> (z, y) |\<in>| R|\<^sup>+|)"
  by (induct rule: ftrancl_induct) (auto, meson ftrancl_into_trancl)

lemma ftranclD2:
  "(x, y) |\<in>| R|\<^sup>+| \<Longrightarrow> \<exists>z. (x = z \<or> (x, z) |\<in>| R|\<^sup>+|) \<and> (z, y) |\<in>| R"
  by (induct rule: ftrancl_induct) auto

lemma not_ftrancl_into:
  "(x, z) |\<notin>| r|\<^sup>+| \<Longrightarrow> (y, z) |\<in>| r \<Longrightarrow> (x, y) |\<notin>| r|\<^sup>+|"
  by transfer (auto simp add: trancl.trancl_into_trancl)
lemmas ftrancl_map_both_fRestr = trancl_map_both_Restr[Transfer.transferred]
lemma ftrancl_map_both_fsubset:
  "finj_on f X \<Longrightarrow> R |\<subseteq>| X |\<times>| X \<Longrightarrow> (map_both f |`| R)|\<^sup>+| = map_both f |`| R|\<^sup>+|"
  using ftrancl_map_both_fRestr[of f X R]
  by (simp add: inf_absorb1)
lemmas ftrancl_map_prod_mono = trancl_map_prod_mono[Transfer.transferred]
lemmas ftrancl_map = trancl_map[Transfer.transferred]


lemmas ffUnion_iff [simp] = Union_iff[Transfer.transferred]
lemmas ffUnionI [intro] = UnionI[Transfer.transferred]
lemmas fUn_simps [simp] = UN_simps[Transfer.transferred]


(* TODO Diff *)
lemmas fINT_simps [simp] = INT_simps[Transfer.transferred]

lemmas fUN_ball_bex_simps [simp] = UN_ball_bex_simps[Transfer.transferred]

(* List *)
lemmas in_fset_conv_nth = in_set_conv_nth[Transfer.transferred]
lemmas fnth_mem [simp] = nth_mem[Transfer.transferred]
lemmas distinct_sorted_list_of_fset = distinct_sorted_list_of_set [Transfer.transferred]
lemmas fcard_fset = card_set[Transfer.transferred]
lemma upt_fset:
  "fset_of_list [i..<j] = fCollect (\<lambda> n. i \<le> n \<and> n < j)"
  by (induct j arbitrary: i) auto

(* Restr *)
abbreviation fRestr :: "('a \<times> 'a) fset \<Rightarrow> 'a fset \<Rightarrow> ('a \<times> 'a) fset" where
  "fRestr r A \<equiv> r |\<inter>| (A |\<times>| A)"

(* Identity on set*)

lift_definition fId_on :: "'a fset \<Rightarrow> ('a \<times> 'a) fset" is Id_on
  using Id_on_subset_Times finite_subset by fastforce

lemmas fId_on_empty [simp] = Id_on_empty [Transfer.transferred]
lemmas fId_on_eqI = Id_on_eqI [Transfer.transferred]
lemmas fId_onI [intro!] = Id_onI [Transfer.transferred]
lemmas fId_onE [elim!] = Id_onE [Transfer.transferred]
lemmas fId_on_iff = Id_on_iff [Transfer.transferred]
lemmas fId_on_fsubset_fTimes = Id_on_subset_Times [Transfer.transferred]

(* Converse*)
lift_definition fconverse :: "('a \<times> 'b) fset \<Rightarrow> ('b \<times> 'a) fset"  ("(_|\<inverse>|)" [1000] 999) is converse by auto

lemmas fconverseI [sym] = converseI [Transfer.transferred]
lemmas fconverseD [sym] = converseD [Transfer.transferred]
lemmas fconverseE [elim!] = converseE [Transfer.transferred]
lemmas fconverse_iff [iff] = converse_iff[Transfer.transferred]
lemmas fconverse_fconverse [simp] = converse_converse[Transfer.transferred]
lemmas fconverse_empty[simp] = converse_empty[Transfer.transferred]

(* injectivity *)

lemmas finj_on_def' = inj_on_def[Transfer.transferred]
lemmas fsubset_finj_on = subset_inj_on[Transfer.transferred]
lemmas the_finv_into_f_f = the_inv_into_f_f[Transfer.transferred]
lemmas f_the_finv_into_f = f_the_inv_into_f[Transfer.transferred]
lemmas the_finv_into_into = the_inv_into_into[Transfer.transferred]
lemmas the_finv_into_onto [simp] = the_inv_into_onto[Transfer.transferred]
lemmas the_finv_into_f_eq = the_inv_into_f_eq[Transfer.transferred]
lemmas the_finv_into_comp = the_inv_into_comp[Transfer.transferred]
lemmas finj_on_the_finv_into = inj_on_the_inv_into [Transfer.transferred]
lemmas finj_on_fUn = inj_on_Un[Transfer.transferred]

lemma finj_Inl_Inr:
  "finj_on Inl A" "finj_on Inr A"
  by (transfer, auto)+
lemma finj_CInl_CInr:
  "finj_on CInl A" "finj_on CInr A"
  using finj_Inl_Inr by force+

lemma finj_Some:
  "finj_on Some A"
  by (transfer, auto)

(* Image *)

lift_definition fImage :: "('a \<times> 'b) fset \<Rightarrow> 'a fset \<Rightarrow> 'b fset" (infixr "|``|" 90) is Image
  using finite_Image by force

lemmas fImage_iff = Image_iff[Transfer.transferred]
lemmas fImage_singleton_iff [iff] = Image_singleton_iff[Transfer.transferred]
lemmas fImageI [intro] = ImageI[Transfer.transferred]
lemmas ImageE [elim!] = ImageE[Transfer.transferred]
lemmas frev_ImageI = rev_ImageI[Transfer.transferred]
lemmas fImage_empty1 [simp] = Image_empty1[Transfer.transferred]
lemmas fImage_empty2 [simp] = Image_empty2[Transfer.transferred]
lemmas fImage_fInt_fsubset = Image_Int_subset[Transfer.transferred]
lemmas fImage_fUn = Image_Un[Transfer.transferred]
lemmas fUn_fImage = Un_Image[Transfer.transferred]
lemmas fImage_fsubset = Image_subset[Transfer.transferred]
lemmas fImage_eq_fUN = Image_eq_UN[Transfer.transferred]
lemmas fImage_mono = Image_mono[Transfer.transferred]
lemmas fImage_fUN = Image_UN[Transfer.transferred]
lemmas fUN_fImage = UN_Image[Transfer.transferred]
lemmas fSigma_fImage = Sigma_Image[Transfer.transferred]


(* fix us *)
lemmas fImage_singleton = Image_singleton[Transfer.transferred]
lemmas fImage_Id_on [simp] = Image_Id_on[Transfer.transferred]
lemmas fImage_Id [simp] = Image_Id[Transfer.transferred]
lemmas fImage_fInt_eq = Image_Int_eq[Transfer.transferred]
lemmas fImage_fsubset_eq = Image_subset_eq[Transfer.transferred]
lemmas fImage_fCollect_case_prod [simp] = Image_Collect_case_prod[Transfer.transferred]
lemmas fImage_fINT_fsubset = Image_INT_subset[Transfer.transferred]
(* Misc *)
lemmas term_fset_induct = term.induct[Transfer.transferred]
lemmas fmap_prod_fimageI = map_prod_imageI[Transfer.transferred]
lemmas finj_on_eq_iff = inj_on_eq_iff[Transfer.transferred]
lemmas prod_fun_fimageE = prod_fun_imageE[Transfer.transferred]

lemma rel_set_cr_fset:
  "rel_set cr_fset = (\<lambda> A B. A = fset ` B)"
proof -
  have "rel_set cr_fset A B \<longleftrightarrow> A = fset ` B" for A B
    by (auto simp: image_def rel_set_def cr_fset_def )
  then show ?thesis by blast
qed
lemma pcr_fset_cr_fset:
  "pcr_fset cr_fset = (\<lambda> x y. x = fset (fset |`| y))"
  unfolding pcr_fset_def rel_set_cr_fset
  unfolding cr_fset_def
  by (auto simp: image_def relcompp_apply)


lemma sorted_list_of_fset_id:
  "sorted_list_of_fset x = sorted_list_of_fset y \<Longrightarrow> x = y"
  by (metis sorted_list_of_fset_simps(2))

(*end *)

lemmas fBall_def = Ball_def[Transfer.transferred]
lemmas fBex_def = Bex_def[Transfer.transferred]
lemmas fCollectE = fCollectD [elim_format]
lemma fCollect_conj_eq:
  "finite (Collect P) \<Longrightarrow> finite (Collect Q) \<Longrightarrow> {|x. P x \<and> Q x|} = fCollect P |\<inter>| fCollect Q"
  by auto

lemma finite_ntrancl:
  "finite R \<Longrightarrow> finite (ntrancl n R)"
  by (induct n) auto

lift_definition nftrancl :: "nat \<Rightarrow> ('a \<times> 'a) fset \<Rightarrow> ('a \<times> 'a) fset" is ntrancl
  by (intro finite_ntrancl) simp

lift_definition frelcomp :: "('a \<times> 'b) fset \<Rightarrow> ('b \<times> 'c) fset \<Rightarrow> ('a \<times> 'c) fset" (infixr "|O|" 75) is relcomp
  by (intro finite_relcomp) simp

lemmas frelcompE[elim!] = relcompE[Transfer.transferred]
lemmas frelcompI[intro] = relcompI[Transfer.transferred]
lemma fId_on_frelcomp_id:
  "fst |`| R |\<subseteq>| S \<Longrightarrow> fId_on S |O| R = R"
  by (auto intro!: frelcompI)
lemma fId_on_frelcomp_id2:
 "snd |`| R |\<subseteq>| S \<Longrightarrow> R |O| fId_on S = R"
  by (auto intro!: frelcompI)


lemmas fimage_fset = image_set[Transfer.transferred]
lemmas ftrancl_Un2_separatorE = trancl_Un2_separatorE[Transfer.transferred]

(* finite vars of term finite function symbols of terms *)

lemma finite_funs_term: "finite (funs_term t)" by (induct t) auto
lemma finite_funas_term: "finite (funas_term t)" by (induct t) auto
lemma finite_vars_ctxt: "finite (vars_ctxt C)" by (induct C) auto

lift_definition ffuns_term :: "('f, 'v) term \<Rightarrow> 'f fset" is funs_term using finite_funs_term
  by blast
lift_definition fvars_term :: "('f, 'v) term \<Rightarrow> 'v fset" is vars_term by simp
lift_definition fvars_ctxt :: "('f, 'v) ctxt \<Rightarrow> 'v fset" is vars_ctxt by (simp add: finite_vars_ctxt)


lemmas fvars_term_ctxt_apply [simp] = vars_term_ctxt_apply[Transfer.transferred]
lemmas fvars_term_of_gterm [simp] = vars_term_of_gterm[Transfer.transferred]
lemmas ground_fvars_term_empty [simp] = ground_vars_term_empty[Transfer.transferred]

lemma ffuns_term_Var [simp]: "ffuns_term (Var x) = {||}"
  by transfer auto
lemma fffuns_term_Fun [simp]: "ffuns_term (Fun f ts) = |\<Union>| (ffuns_term |`| fset_of_list ts) |\<union>| {|f|}"
  by transfer auto

lemma fvars_term_Var [simp]: "fvars_term (Var x) = {|x|}"
  by transfer auto
lemma fvars_term_Fun [simp]: "fvars_term (Fun f ts) = |\<Union>| (fvars_term |`| fset_of_list ts)"
  by transfer auto

lift_definition ffunas_term :: "('f, 'v) term \<Rightarrow> ('f \<times> nat) fset" is funas_term
  by (simp add: finite_funas_term)
lift_definition ffunas_gterm :: "'f gterm \<Rightarrow> ('f \<times> nat) fset" is funas_gterm
  by (simp add: finite_funas_gterm)

lemmas ffunas_term_simps [simp] = funas_term.simps[Transfer.transferred]
lemmas ffunas_gterm_simps [simp] = funas_gterm.simps[Transfer.transferred]
lemmas ffunas_term_of_gterm_conv = funas_term_of_gterm_conv[Transfer.transferred]
lemmas ffunas_gterm_gterm_of_term = funas_gterm_gterm_of_term[Transfer.transferred]


lemma sorted_list_of_fset_fimage_dist:
  "sorted_list_of_fset (f |`| A) = sort (remdups (map f (sorted_list_of_fset A)))"
  by (auto simp: sorted_list_of_fset.rep_eq simp flip: sorted_list_of_set_sort_remdups)

end

(* Move me *)
lemma finite_snd [intro]:
  "finite S \<Longrightarrow> finite {x. (y, x) \<in> S}"
  by (induct S rule: finite.induct) auto

lemma finite_Collect_less_eq:
  "Q \<le> P \<Longrightarrow> finite (Collect P) \<Longrightarrow> finite (Collect Q)"
  by (metis (full_types) Ball_Collect infinite_iff_countable_subset rev_predicate1D)


datatype 'a FSet_Lex_Wrapper = Wrapp (ex: "'a fset")

lemma inj_FSet_Lex_Wrapper: "inj Wrapp"
  unfolding inj_def by auto

lemmas ftrancl_map_both = inj_on_trancl_map_both[Transfer.transferred]

instantiation FSet_Lex_Wrapper :: (linorder) linorder
begin

definition less_eq_FSet_Lex_Wrapper :: "('a :: linorder) FSet_Lex_Wrapper \<Rightarrow> 'a FSet_Lex_Wrapper \<Rightarrow> bool"
  where "less_eq_FSet_Lex_Wrapper S T =
    (let S' = sorted_list_of_fset (ex S) in
     let T' = sorted_list_of_fset (ex T) in
     S' \<le> T')"

definition less_FSet_Lex_Wrapper :: "'a FSet_Lex_Wrapper \<Rightarrow> 'a FSet_Lex_Wrapper \<Rightarrow> bool"
  where "less_FSet_Lex_Wrapper S T =
    (let S' = sorted_list_of_fset (ex S) in
     let T' = sorted_list_of_fset (ex T) in
     S' < T')"

instance by (intro_classes)
   (auto simp: less_eq_FSet_Lex_Wrapper_def less_FSet_Lex_Wrapper_def ex_def FSet_Lex_Wrapper.expand dest: sorted_list_of_fset_id)
end


end