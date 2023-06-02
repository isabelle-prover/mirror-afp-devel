theory NonInterference
  imports Soundness
begin

fun low_list where
  "low_list [] = Bool Btrue"
| "low_list (v # q) = And (LowExp (Evar v)) (low_list q)"

lemma low_listE:
  assumes "(s1, h1), (s2, h2) \<Turnstile> low_list l"
      and "x \<in> set l"
    shows "s1 x = s2 x"
  using assms
proof (induct l)
  case (Cons a l)
  then show ?case
  proof (cases "x = a")
    case True
    then have "(s1, h1), (s2, h2) \<Turnstile> LowExp (Evar a)"
      using Cons.prems(1) by auto
    then show ?thesis
      by (simp add: True)
  next
    case False
    then show ?thesis
      using Cons.hyps Cons.prems(1) Cons.prems(2) by auto
  qed
qed (simp)

lemma low_listI:
  assumes "\<And>x. x \<in> set l \<Longrightarrow> s1 x = s2 x"
  shows "(s1, h1), (s2, h2) \<Turnstile> low_list l"
  using assms
by (induct l) simp_all

corollary non_interference:
  assumes "(None :: ('i, 'a, nat) cont) \<turnstile> {And P (low_list In)} C {low_list Out}"
      and "red_rtrans C (s1, normalize (get_fh H1)) Cskip (s1', h1')"
      and "red_rtrans C (s2, normalize (get_fh H2)) Cskip (s2', h2')"
      and "\<And>x. x \<in> set In \<Longrightarrow> s1 x = s2 x"
      and "x \<in> set Out"
      and "(s1, H1), (s2, H2) \<Turnstile> P"
      and "full_ownership (get_fh H1) \<and> no_guard H1"
      and "full_ownership (get_fh H2) \<and> no_guard H2"
    shows "s1' x = s2' x"
proof -
  have "\<exists>H1' H2'. no_guard H1' \<and> full_ownership (get_fh H1') \<and> snd (s1', h1') = FractionalHeap.normalize (get_fh H1') \<and>
   no_guard H2' \<and> full_ownership (get_fh H2') \<and> snd (s2', h2') = FractionalHeap.normalize (get_fh H2')
  \<and> (fst (s1', h1'), H1'), (fst (s2', h2'), H2') \<Turnstile> (low_list Out :: ('i, 'a, nat) assertion)"
  proof (rule safety_no_frame(3))
    show "(None :: ('i, 'a, nat) cont) \<Turnstile> {And P (low_list In)} C {low_list Out}"
      using assms(1) soundness by blast
    have "(s1, H1), (s2, H2) \<Turnstile> low_list In"
      by (simp add: assms(4) low_listI)
    then show "(s1, H1), (s2, H2) \<Turnstile> And P (low_list In)"
      by (simp add: assms(6))
  qed ((insert assms; blast)+)
  then show ?thesis
    by (metis assms(5) fst_conv low_listE)
qed

definition heapify where
  "heapify h = (\<lambda>l. apply_opt (\<lambda>v. (pwrite, v)) (h l), None, \<lambda>_. None)"

lemma heapify_properties:
  "full_ownership (get_fh (heapify h))"
  "no_guard (heapify h)"
  "normalize (get_fh (heapify h)) = h"
proof (rule full_ownershipI)
  fix l p assume "get_fh (heapify h) l = Some p"
  then show "fst p = pwrite"
    by (metis apply_opt.elims fst_conv get_fh.elims heapify_def option.sel option.simps(3))
next
  show "no_guard (heapify h)"
    by (metis addition_cancellative decompose_guard_remove_easy decompose_heap_triple heapify_def neutral_add no_guards_remove snd_conv)
  show "normalize (get_fh (heapify h)) = h"
  proof (rule ext)
    fix l show "FractionalHeap.normalize (get_fh (heapify h)) l = h l"
    proof (cases "h l")
      case None
      then show ?thesis
        by (metis apply_opt.simps(1) domIff dom_normalize fst_conv get_fh.simps heapify_def)
    next
      case (Some a)
      then show ?thesis
        by (simp add: FractionalHeap.normalize_eq(2) heapify_def)
    qed
  qed
qed

corollary non_interference_no_precondition:
  assumes "(None :: ('i, 'a, nat) cont) \<turnstile> {low_list In} C {low_list Out}"
      and "red_rtrans C (s1, h1) Cskip (s1', h1')"
      and "red_rtrans C (s2, h2) Cskip (s2', h2')"
      and "\<And>x. x \<in> set In \<Longrightarrow> s1 x = s2 x"
      and "x \<in> set Out"
    shows "s1' x = s2' x"
proof (rule non_interference)
  show "(None :: ('i, 'a, nat) cont) \<turnstile> {And (Bool Btrue) (low_list In)} C {low_list Out}"
    using RuleCons assms(1) entails_def hyper_sat.simps(3) by blast
  show "red_rtrans C (s1, FractionalHeap.normalize (get_fh (heapify h1))) Cskip (s1', h1')"
    by (metis assms(2) heapify_properties(3))
  show "red_rtrans C (s2, FractionalHeap.normalize (get_fh (heapify h2))) Cskip (s2', h2')"
    by (metis assms(3) heapify_properties(3))
qed (insert assms heapify_properties; auto)+


end