(*  Title:       Extension of Stateful Intransitive Noninterference with Inputs, Outputs, and Nondeterminism in Language IMP
    Author:      Pasquale Noce
                 Senior Staff Firmware Engineer at HID Global, Italy
                 pasquale dot noce dot lavoro at gmail dot com
                 pasquale dot noce at hidglobal dot com
*)

section "Idempotence of the auxiliary type system meant for loop bodies"

theory Idempotence
  imports Definitions
begin

text \<open>
\null

As in my previous paper \<^cite>\<open>"Noce24"\<close>, the purpose of this section is to prove that the auxiliary
type system @{const [names_short] noninterf.ctyping1} used to simulate the execution of loop bodies
is idempotent, namely that if its output for a given input is the pair formed by @{typ "state set"}
@{term B} and @{typ "vname set"} @{term Y}, then the output is the same if @{term B} and @{term Y}
are fed back into the type system (lemma @{text ctyping1_idem}).
\<close>


subsection "Local context proofs"

context noninterf
begin


abbreviation ctyping1_idem_lhs where
"ctyping1_idem_lhs s t t' ys ys' x \<equiv>
  if [y\<leftarrow>ys'. fst y = x] = []
  then if [y\<leftarrow>ys. fst y = x] = []
    then s x
    else case snd (last [y\<leftarrow>ys. fst y = x]) of None \<Rightarrow> t x | Some i \<Rightarrow> i
  else case snd (last [y\<leftarrow>ys'. fst y = x]) of None \<Rightarrow> t' x | Some i \<Rightarrow> i"

abbreviation ctyping1_idem_rhs where
"ctyping1_idem_rhs f s t x \<equiv>
  if f x = []
  then s x
  else case snd (last (f x)) of None \<Rightarrow> t x | Some i \<Rightarrow> i"

abbreviation ctyping1_idem_pred where
"ctyping1_idem_pred s t t' ys ys' A (S :: state_upd list set) \<equiv> \<exists>f s'.
  (\<exists>t''. ctyping1_idem_lhs s t t' ys ys' = ctyping1_idem_rhs f s' t'') \<and>
  (\<forall>x. (f x = [] \<longleftrightarrow> [y\<leftarrow>ys @ ys'. fst y = x] = []) \<and>
    (f x \<noteq> [] \<longrightarrow> last (f x) = last [y\<leftarrow>ys @ ys'. fst y = x])) \<and>
  (\<exists>ys''. f = (\<lambda>x. [y\<leftarrow>ys''. fst y = x]) \<and> ys'' \<in> S) \<and> s' \<in> A"


lemma ctyping1_merge_aux_no_nil:
 "ws \<in> A \<Squnion> B \<Longrightarrow> ws \<noteq> []"
by (erule ctyping1_merge_aux.cases, simp_all)

lemma ctyping1_merge_aux_empty_lhs:
 "{} \<Squnion> B = {[(ys, False)] | ys. ys \<in> B}"
by (rule equalityI, clarify, erule ctyping1_merge_aux.induct, auto)

lemma ctyping1_merge_aux_empty_rhs:
 "A \<Squnion> {} = {[(xs, True)] | xs. xs \<in> A}"
by (rule equalityI, clarify, erule ctyping1_merge_aux.induct, auto)

lemma ctyping1_merge_empty_lhs:
 "{} \<squnion> B = B"
by (force simp: ctyping1_merge_def ctyping1_merge_aux_empty_lhs)

lemma ctyping1_merge_empty_rhs:
 "A \<squnion> {} = A"
by (force simp: ctyping1_merge_def ctyping1_merge_aux_empty_rhs)

lemma ctyping1_aux_nonempty:
 "\<turnstile> c \<noteq> {}"
by (induction c, auto simp: Let_def ctyping1_merge_def
 ctyping1_merge_append_def ctyping1_append_def, fastforce)


lemma ctyping1_merge_idem_fst:
  assumes
    A: "\<And>ys ys'. ys \<in> \<turnstile> c\<^sub>1 \<Longrightarrow> ys' \<in> \<turnstile> c\<^sub>1 \<Longrightarrow>
      ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>1)" and
    B: "\<And>ys ys'. ys \<in> \<turnstile> c\<^sub>2 \<Longrightarrow> ys' \<in> \<turnstile> c\<^sub>2 \<Longrightarrow>
      ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>2)" and
    C: "s \<in> A" and
    D: "ys \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2" and
    E: "ys' \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2"
  shows "ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2)"
proof -
  obtain ws where "ws \<in> \<turnstile> c\<^sub>1 \<Squnion> \<turnstile> c\<^sub>2" and "ys = concat (map fst ws)"
    using D by (auto simp: ctyping1_merge_def)
  thus ?thesis
  proof (induction ws arbitrary: ys rule: list.induct,
   blast dest: ctyping1_merge_aux_no_nil)
    fix w ws ys
    assume
      F: "\<And>xs. ws \<in> \<turnstile> c\<^sub>1 \<Squnion> \<turnstile> c\<^sub>2 \<Longrightarrow> xs = concat (map fst ws) \<Longrightarrow>
        ctyping1_idem_pred s t t' xs ys' A (\<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2)" and
      G: "w # ws \<in> \<turnstile> c\<^sub>1 \<Squnion> \<turnstile> c\<^sub>2"
    assume "ys = concat (map fst (w # ws))"
    hence H: "ys = fst w @ concat (map fst ws)"
      (is "ys = ?x @ ?xs")
      by simp
    have "ctyping1_idem_pred s t t' ?xs ys' A (\<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2)"
    proof (cases ws)
      case Nil
      show ?thesis
        apply (rule exI [of _ "\<lambda>x. [y\<leftarrow>ys'. fst y = x]"])
        apply (rule exI [of _ s])
        apply (rule conjI)
         apply (rule exI [of _ t'])
        by (auto simp: C E Nil)
    next
      case Cons
      have "ws \<in> \<turnstile> c\<^sub>1 \<Squnion> \<turnstile> c\<^sub>2"
        using G by (rule ctyping1_merge_aux.cases, simp_all add: Cons)
      thus ?thesis
        using F by simp
    qed
    then obtain f and s' and t'' and ys'' where
      I: "ctyping1_idem_lhs s t t' ?xs ys' =
        ctyping1_idem_rhs f s' t''" and
      J: "\<forall>x. (f x = [] \<longleftrightarrow> [y\<leftarrow>?xs @ ys'. fst y = x] = []) \<and>
        (f x \<noteq> [] \<longrightarrow> last (f x) = last [y\<leftarrow>?xs @ ys'. fst y = x])" and
      K: "f = (\<lambda>x. [y\<leftarrow>ys''. fst y = x])" and
      L: "ys'' \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2" and
      M: "s' \<in> A"
      by auto
    obtain ws'' where
      N: "ws'' \<in> \<turnstile> c\<^sub>1 \<Squnion> \<turnstile> c\<^sub>2" and
      O: "ys'' = concat (map fst ws'')"
      using L by (auto simp: ctyping1_merge_def)
    show "ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2)"
    proof (cases "w \<in> set ws''")
      assume P: "w \<in> set ws''"
      show ?thesis
        apply (rule exI [of _ f])
        apply (rule exI [of _ s'])
        apply (rule conjI)
         apply (rule exI [of _ t''])
         apply (rule ext)
        subgoal for x
        proof (cases "[y\<leftarrow>ys'. fst y = x]", cases "[y\<leftarrow>ys. fst y = x] = []")
          case Cons
          thus "ctyping1_idem_lhs s t t' ys ys' x =
            ctyping1_idem_rhs f s' t'' x"
            by (insert fun_cong [OF I, of x], simp)
        next
          case Nil
          moreover case True
          ultimately show "ctyping1_idem_lhs s t t' ys ys' x =
            ctyping1_idem_rhs f s' t'' x"
            using H by (insert fun_cong [OF I, of x], simp)
        next
          case Nil
          case False
          hence "[y\<leftarrow>?x. fst y = x] \<noteq> [] \<or> [y\<leftarrow>?xs. fst y = x] \<noteq> []"
            using H by simp
          moreover {
            assume "[y\<leftarrow>?x. fst y = x] \<noteq> []"
            hence "[y\<leftarrow>ys''. fst y = x] \<noteq> []"
              using O and P by (auto simp: filter_concat)
            hence "[y\<leftarrow>?xs. fst y = x] \<noteq> []"
              using J and K and Nil by simp
          }
          ultimately have Q: "[y\<leftarrow>?xs. fst y = x] \<noteq> []" ..
          hence "(case snd (last [y\<leftarrow>?xs. fst y = x]) of
            None \<Rightarrow> t x | Some i \<Rightarrow> i) = ctyping1_idem_rhs f s' t'' x"
            using Nil by (insert fun_cong [OF I, of x], simp)
          moreover have "last [y\<leftarrow>?xs. fst y = x] = last [y\<leftarrow>ys. fst y = x]"
            using H and Q by simp
          ultimately show "ctyping1_idem_lhs s t t' ys ys' x =
            ctyping1_idem_rhs f s' t'' x"
            using Nil and False by simp
        qed
        apply (rule conjI)
        subgoal
        proof -
          show "\<forall>x. (f x = [] \<longleftrightarrow> [y\<leftarrow>ys @ ys'. fst y = x] = []) \<and>
            (f x \<noteq> [] \<longrightarrow> last (f x) = last [y\<leftarrow>ys @ ys'. fst y = x])"
            (is "\<forall>x. ?P x \<and> ?Q x")
          proof
            fix x
            have "?P x"
            proof
              assume Q: "f x = []"
              hence "[y\<leftarrow>?xs @ ys'. fst y = x] = []"
                using J by simp
              moreover have "[y\<leftarrow>?x. fst y = x] = []"
                using K and O and P and Q by (simp add: filter_concat)
              ultimately show "[y\<leftarrow>ys @ ys'. fst y = x] = []"
                using H by simp
            qed (insert H J, simp)
            moreover have "?Q x"
              using J and H by simp
            ultimately show "?P x \<and> ?Q x" ..
          qed
        qed
        by (insert K L M, blast)
    next
      assume P: "w \<notin> set ws''"
      let ?y = "fst (hd ws'')"
      show ?thesis
      proof (cases "snd w = snd (hd ws'')")
        assume Q: "snd w = snd (hd ws'')"
        hence "snd w \<and> snd (hd ws'') \<or> \<not> snd w \<and> \<not> snd (hd ws'')"
          (is "?P \<or> ?Q")
          by simp
        moreover {
          assume ?P
          have "?x \<in> \<turnstile> c\<^sub>1"
            using G by (rule ctyping1_merge_aux.cases, insert `?P`, simp_all)
          moreover have "?y \<in> \<turnstile> c\<^sub>1"
            using N by (rule ctyping1_merge_aux.cases, insert `?P`, simp_all)
          ultimately have "ctyping1_idem_pred s t t' ?x ?y A (\<turnstile> c\<^sub>1)"
            using A by simp
        }
        moreover {
          assume ?Q
          have "?x \<in> \<turnstile> c\<^sub>2"
            using G by (rule ctyping1_merge_aux.cases, insert `?Q`, simp_all)
          moreover have "?y \<in> \<turnstile> c\<^sub>2"
            using N by (rule ctyping1_merge_aux.cases, insert `?Q`, simp_all)
          ultimately have "ctyping1_idem_pred s t t' ?x ?y A (\<turnstile> c\<^sub>2)"
            using B by simp
        }
        ultimately obtain f\<^sub>0 and s\<^sub>0 and t\<^sub>0 and ys\<^sub>0 where
          R: "ctyping1_idem_lhs s t t' ?x ?y =
            ctyping1_idem_rhs f\<^sub>0 s\<^sub>0 t\<^sub>0" and
          S: "\<forall>x. (f\<^sub>0 x = [] \<longleftrightarrow> [y\<leftarrow>?x @ ?y. fst y = x] = []) \<and>
            (f\<^sub>0 x \<noteq> [] \<longrightarrow> last (f\<^sub>0 x) = last [y\<leftarrow>?x @ ?y. fst y = x])" and
          T: "f\<^sub>0 = (\<lambda>x. [y\<leftarrow>ys\<^sub>0. fst y = x])" and
          U: "ys\<^sub>0 \<in> \<turnstile> c\<^sub>1 \<and> snd w \<or> ys\<^sub>0 \<in> \<turnstile> c\<^sub>2 \<and> \<not> snd w"
          by auto
        from U obtain w\<^sub>0 where
          V: "[w\<^sub>0] \<in> \<turnstile> c\<^sub>1 \<Squnion> \<turnstile> c\<^sub>2" and
          W: "ys\<^sub>0 = fst w\<^sub>0" and
          X: "snd w\<^sub>0 = snd w"
          by fastforce
        show ?thesis
        proof (cases "w\<^sub>0 \<in> set ws''")
          assume Y: "w\<^sub>0 \<in> set ws''"
          show ?thesis
            apply (rule exI [of _ f])
            apply (rule exI [of _ s'])
            apply (rule conjI)
             apply (rule exI [of _ t''])
             apply (rule ext)
            subgoal for x
            proof (cases "[y\<leftarrow>ys'. fst y = x]", cases "[y\<leftarrow>ys. fst y = x] = []")
              case Cons
              thus "ctyping1_idem_lhs s t t' ys ys' x =
                ctyping1_idem_rhs f s' t'' x"
                by (insert fun_cong [OF I, of x], simp)
            next
              case Nil
              moreover case True
              ultimately show "ctyping1_idem_lhs s t t' ys ys' x =
                ctyping1_idem_rhs f s' t'' x"
                using H by (insert fun_cong [OF I, of x], simp)
            next
              case Nil
              case False
              hence "[y\<leftarrow>?x. fst y = x] \<noteq> [] \<or> [y\<leftarrow>?xs. fst y = x] \<noteq> []"
                using H by simp
              moreover {
                assume "[y\<leftarrow>?x. fst y = x] \<noteq> []"
                hence "[y\<leftarrow>ys\<^sub>0. fst y = x] \<noteq> []"
                  using S and T by simp
                hence "[y\<leftarrow>ys''. fst y = x] \<noteq> []"
                using O and W and Y by (auto simp: filter_concat)
                hence "[y\<leftarrow>?xs. fst y = x] \<noteq> []"
                  using J and K and Nil by simp
              }
              ultimately have Z: "[y\<leftarrow>?xs. fst y = x] \<noteq> []" ..
              hence "(case snd (last [y\<leftarrow>?xs. fst y = x]) of
                None \<Rightarrow> t x | Some i \<Rightarrow> i) = ctyping1_idem_rhs f s' t'' x"
                using Nil by (insert fun_cong [OF I, of x], simp)
              moreover have "last [y\<leftarrow>?xs. fst y = x] = last [y\<leftarrow>ys. fst y = x]"
                using H and Z by simp
              ultimately show "ctyping1_idem_lhs s t t' ys ys' x =
                ctyping1_idem_rhs f s' t'' x"
                using Nil and False by simp
            qed
            apply (rule conjI)
            subgoal
            proof -
              show "\<forall>x. (f x = [] \<longleftrightarrow> [y\<leftarrow>ys @ ys'. fst y = x] = []) \<and>
                (f x \<noteq> [] \<longrightarrow> last (f x) = last [y\<leftarrow>ys @ ys'. fst y = x])"
                (is "\<forall>x. ?P x \<and> ?Q x")
              proof
                fix x
                have "?P x"
                proof
                  assume Z: "f x = []"
                  hence "[y\<leftarrow>?xs @ ys'. fst y = x] = []"
                    using J by simp
                  moreover have "[y\<leftarrow>ys''. fst y = x] = []"
                    using K and Z by simp
                  hence "[y\<leftarrow>ys\<^sub>0. fst y = x] = []"
                    using O and W and Y by (simp add: filter_concat)
                  hence "[y\<leftarrow>?x. fst y = x] = []"
                    using S and T by simp
                  ultimately show "[y\<leftarrow>ys @ ys'. fst y = x] = []"
                    using H by simp
                qed (insert H J, simp)
                moreover have "?Q x"
                  using J and H by simp
                ultimately show "?P x \<and> ?Q x" ..
              qed
            qed
            by (insert K L M, blast)
        next
          assume Y: "w\<^sub>0 \<notin> set ws''"
          let ?ws = "w\<^sub>0 # tl ws''"
          {
            assume Z: "tl ws'' \<noteq> []"
            have "tl ws'' \<in> \<turnstile> c\<^sub>1 \<Squnion> \<turnstile> c\<^sub>2"
              using N by (rule ctyping1_merge_aux.cases, insert Z, simp_all)
            moreover have "snd (hd (tl ws'')) = (\<not> snd w)"
              using N by (rule ctyping1_merge_aux.cases, insert Q Z, simp_all)
            moreover have "w\<^sub>0 \<notin> set (tl ws'')"
              using Y by (cases ws'', simp_all)
            ultimately have "?ws \<in> \<turnstile> c\<^sub>1 \<Squnion> \<turnstile> c\<^sub>2"
              by (cases w\<^sub>0, insert U W X, auto)
          }
          hence Z: "?ws \<in> \<turnstile> c\<^sub>1 \<Squnion> \<turnstile> c\<^sub>2"
            by (cases "tl ws''", insert V, simp_all)
          let ?ys = "concat (map fst (tl ws''))"
          let ?f = "\<lambda>x. [y\<leftarrow>concat (map fst ?ws). fst y = x]"
          let ?t = "\<lambda>x. if f x = [] then t\<^sub>0 x else t'' x"
          have AA: "ws'' = hd ws'' # tl ws''"
            by (insert ctyping1_merge_aux_no_nil [OF N], simp)
          have AB: "ys'' = ?y @ ?ys"
            using O by (subst (asm) AA, simp)
          have AC: "\<forall>x. [y\<leftarrow>?ys. fst y = x] \<noteq> [] \<longrightarrow>
            last (?f x) = last (f x)"
            using K and O by (subst (asm) AA, simp)
          have AD: "\<forall>x. [y\<leftarrow>?ys. fst y = x] = [] \<and> [y\<leftarrow>?y. fst y = x] \<noteq> [] \<longrightarrow>
            last (?f x) = last (f x)"
            (is "\<forall>x. ?P x \<and> ?Q x \<longrightarrow> _")
          proof clarify
            fix x
            assume "?P x" and "?Q x"
            moreover from this and S and T have
             "last [y\<leftarrow>ys\<^sub>0. fst y = x] = last [y\<leftarrow>?x @ ?y. fst y = x]"
              by simp
            ultimately show "last (?f x) = last (f x)"
              using K and W and AB by simp
          qed
          show ?thesis
            apply (rule exI [of _ ?f])
            apply (rule exI [of _ s'])
            apply (rule conjI)
             apply (rule exI [of _ ?t])
             apply (rule ext)
            subgoal for x
            proof (cases "[y\<leftarrow>ys'. fst y = x]", cases "[y\<leftarrow>?xs. fst y = x] = []")
              case Cons
              hence AE:
               "(case snd (last [y\<leftarrow>ys'. fst y = x]) of
                  None \<Rightarrow> t' x | Some i \<Rightarrow> i) =
                (case snd (last (f x)) of None \<Rightarrow> ?t x | Some i \<Rightarrow> i)"
                using J by (insert fun_cong [OF I, of x], simp)
              show "ctyping1_idem_lhs s t t' ys ys' x =
                ctyping1_idem_rhs ?f s' ?t x"
              proof (cases "[y\<leftarrow>?ys. fst y = x] \<noteq> []")
                case True
                thus ?thesis
                  using AC and AE and Cons by simp
              next
                case False
                moreover have "[y\<leftarrow>ys''. fst y = x] \<noteq> []"
                  using J and K and Cons by simp
                ultimately have "[y\<leftarrow>?y. fst y = x] \<noteq> []"
                  using AB by simp
                moreover from this have "?f x \<noteq> []"
                  using S and T and W by simp
                ultimately show ?thesis
                  using AD and AE and Cons and False by simp
              qed
            next
              case Nil
              moreover case False
              ultimately have
               "(case snd (last [y\<leftarrow>ys. fst y = x]) of
                  None \<Rightarrow> t x | Some i \<Rightarrow> i) =
                (case snd (last (f x)) of None \<Rightarrow> ?t x | Some i \<Rightarrow> i)"
                using J and H by (insert fun_cong [OF I, of x], simp)
              moreover have
                AE: "[y\<leftarrow>?y. fst y = x] \<noteq> [] \<or> [y\<leftarrow>?ys. fst y = x] \<noteq> []"
                (is "_ \<or> ?P")
                using J and K and AB and False by auto
              hence "?f x \<noteq> []"
                using S and T and W by (cases ?P, simp_all)
              moreover have "last (?f x) = last (f x)"
                using AC and AD and AE by blast
              ultimately show "ctyping1_idem_lhs s t t' ys ys' x =
                ctyping1_idem_rhs ?f s' ?t x"
                using H and Nil and False by auto
            next
              case Nil
              moreover case True
              ultimately have AE: "f x = []"
                using J by simp
              hence AF: "[y\<leftarrow>?y @ ?ys. fst y = x] = []"
                using K and AB by simp
              show "ctyping1_idem_lhs s t t' ys ys' x =
                ctyping1_idem_rhs ?f s' ?t x"
              proof (cases "[y\<leftarrow>?x. fst y = x] = []")
                assume AG: "[y\<leftarrow>?x. fst y = x] = []"
                moreover from J and AE have "s x = s' x"
                  by (insert fun_cong [OF I, of x], simp)
                moreover have "[y\<leftarrow>ys\<^sub>0. fst y = x] = []"
                  using S and T and AF and AG by simp
                hence "?f x = []"
                  using W and AF by simp
                ultimately show ?thesis
                  using H and Nil and True by simp
              next
                assume AG: "[y\<leftarrow>?x. fst y = x] \<noteq> []"
                moreover from this and S and AE and AF have
                 "(case snd (last [y\<leftarrow>?x. fst y = x]) of
                    None \<Rightarrow> t x | Some i \<Rightarrow> i) =
                  (case snd (last (f\<^sub>0 x)) of None \<Rightarrow> ?t x | Some i \<Rightarrow> i)"
                  by (insert fun_cong [OF R, of x], simp)
                moreover have "[y\<leftarrow>ys\<^sub>0. fst y = x] \<noteq> []"
                  using S and T and AG by simp
                hence "?f x \<noteq> []"
                  using W by simp
                moreover have "last (?f x) = last (f\<^sub>0 x)"
                  using T and W and AF by simp
                ultimately show ?thesis
                  using H and Nil and True by auto
              qed
            qed
            apply (rule conjI)
            subgoal
            proof -
              show "\<forall>x. (?f x = [] \<longleftrightarrow> [y\<leftarrow>ys @ ys'. fst y = x] = []) \<and>
                (?f x \<noteq> [] \<longrightarrow> last (?f x) = last [y\<leftarrow>ys @ ys'. fst y = x])"
                (is "\<forall>x. ?P x \<and> ?Q x")
              proof
                fix x
                have AE: "?P x"
                proof
                  assume AF: "?f x = []"
                  hence "[y\<leftarrow>?x @ ?y. fst y = x] = []"
                    using S and T and W by simp
                  moreover from this and J and K and AB and AF have
                   "[y\<leftarrow>?xs @ ys'. fst y = x] = []"
                    by auto
                  ultimately show "[y\<leftarrow>ys @ ys'. fst y = x] = []"
                    using H by simp
                next
                  assume "[y\<leftarrow>ys @ ys'. fst y = x] = []"
                  hence "[y\<leftarrow>?x @ ?y @ ?ys. fst y = x] = []"
                    using H and J and K and AB by simp
                  moreover from this have "[y\<leftarrow>ys\<^sub>0. fst y = x] = []"
                    using S and T by simp
                  ultimately show "?f x = []"
                    using W by simp
                qed
                moreover have "?Q x"
                proof (clarify, cases "[y\<leftarrow>?y @ ?ys. fst y = x]")
                  case Nil
                  hence "last (?f x) = last (f\<^sub>0 x)"
                    using T and W by simp
                  moreover assume "?f x \<noteq> []"
                  hence "[y\<leftarrow>ys @ ys'. fst y = x] \<noteq> []"
                    using AE by blast
                  hence "[y\<leftarrow>?x @ ?y @ ?ys. fst y = x] \<noteq> []"
                    using H and J and K and AB by simp
                  ultimately have "last (?f x) = last [y\<leftarrow>?x. fst y = x]"
                    using S and Nil by simp
                  moreover have "[y\<leftarrow>?xs @ ys'. fst y = x] = []"
                    using J and K and AB and Nil by simp
                  ultimately show
                   "last (?f x) = last [y\<leftarrow>ys @ ys'. fst y = x]"
                    using H by simp
                next
                  case Cons
                  hence "[y\<leftarrow>?y. fst y = x] \<noteq> [] \<or>
                    [y\<leftarrow>?ys. fst y = x] \<noteq> []"
                    by auto
                  hence "last (?f x) = last (f x)"
                    using AC and AD by blast
                  moreover have "f x \<noteq> []"
                    using K and AB and Cons by simp
                  ultimately show
                   "last (?f x) = last [y\<leftarrow>ys @ ys'. fst y = x]"
                    using H and J by simp
                qed
                ultimately show "?P x \<and> ?Q x" ..
              qed
            qed
            by (rule conjI, rule exI [of _ "concat (map fst ?ws)"],
             insert M Z, auto simp only: ctyping1_merge_def)
        qed
      next
        assume "snd w \<noteq> snd (hd ws'')"
        hence "snd w \<and> \<not> snd (hd ws'') \<or> \<not> snd w \<and> snd (hd ws'')"
          (is "?P \<or> ?Q")
          by simp
        moreover {
          assume ?P
          moreover have "?x \<in> \<turnstile> c\<^sub>1"
            using G by (rule ctyping1_merge_aux.cases, insert `?P`, simp_all)
          moreover have "(?x, True) \<notin> set ws''"
            using P and `?P` by (cases w, simp)
          ultimately have "w # ws'' \<in> \<turnstile> c\<^sub>1 \<Squnion> \<turnstile> c\<^sub>2"
            using N by (cases w, auto)
        }
        moreover {
          assume ?Q
          moreover have "?x \<in> \<turnstile> c\<^sub>2"
            using G by (rule ctyping1_merge_aux.cases, insert `?Q`, simp_all)
          moreover have "(?x, False) \<notin> set ws''"
            using P and `?Q` by (cases w, simp)
          ultimately have "w # ws'' \<in> \<turnstile> c\<^sub>1 \<Squnion> \<turnstile> c\<^sub>2"
            using N by (cases w, auto)
        }
        ultimately have Q: "w # ws'' \<in> \<turnstile> c\<^sub>1 \<Squnion> \<turnstile> c\<^sub>2"
          (is "?ws \<in> _") ..
        let ?f = "\<lambda>x. [y\<leftarrow>concat (map fst ?ws). fst y = x]"
        let ?t = "\<lambda>x. if f x = [] then t x else t'' x"
        show ?thesis
          apply (rule exI [of _ ?f])
          apply (rule exI [of _ s'])
          apply (rule conjI)
           apply (rule exI [of _ ?t])
           apply (rule ext)
          subgoal for x
          proof (cases "[y\<leftarrow>ys'. fst y = x]", cases "[y\<leftarrow>?xs. fst y = x] = []")
            case Cons
            moreover from this have
             "(case snd (last [y\<leftarrow>ys'. fst y = x]) of
                None \<Rightarrow> t' x | Some i \<Rightarrow> i) =
              (case snd (last (f x)) of None \<Rightarrow> ?t x | Some i \<Rightarrow> i)"
              using J by (insert fun_cong [OF I, of x], simp)
            moreover have "?f x \<noteq> []"
              using J and K and O and Cons by simp
            moreover have "f x \<noteq> []"
              using J and Cons by simp
            hence "last (?f x) = last (f x)"
              using K and O by simp
            ultimately show "ctyping1_idem_lhs s t t' ys ys' x =
              ctyping1_idem_rhs ?f s' ?t x"
              by auto
          next
            case Nil
            moreover case False
            ultimately have
             "(case snd (last [y\<leftarrow>ys. fst y = x]) of
                None \<Rightarrow> t x | Some i \<Rightarrow> i) =
              (case snd (last (f x)) of None \<Rightarrow> ?t x | Some i \<Rightarrow> i)"
              using J and H by (insert fun_cong [OF I, of x], simp)
            moreover have "?f x \<noteq> []"
              using J and K and O and False by simp
            moreover have "f x \<noteq> []"
              using J and False by simp
            hence "last (?f x) = last (f x)"
              using K and O by simp
            ultimately show "ctyping1_idem_lhs s t t' ys ys' x =
              ctyping1_idem_rhs ?f s' ?t x"
              using H and Nil and False by auto
          next
            case Nil
            moreover case True
            ultimately have R: "f x = []"
              using J by simp
            show "ctyping1_idem_lhs s t t' ys ys' x =
              ctyping1_idem_rhs ?f s' ?t x"
            proof (cases "[y\<leftarrow>?x. fst y = x] = []")
              assume "[y\<leftarrow>?x. fst y = x] = []"
              moreover have "[y\<leftarrow>ys''. fst y = x] = []"
                using K and R by simp
              ultimately have "?f x = []"
                using O by simp
              moreover from J and R have "s x = s' x"
                by (insert fun_cong [OF I, of x], simp)
              ultimately show ?thesis
                using H and Nil and True by simp
            next
              assume "[y\<leftarrow>?x. fst y = x] \<noteq> []"
              moreover have "last [y\<leftarrow>ys. fst y = x] = last [y\<leftarrow>?x. fst y = x]"
                using H and True by simp
              moreover have "last (?f x) = last [y\<leftarrow>?x. fst y = x]"
                using K and O and R by simp
              ultimately show ?thesis
                using H and R and Nil by simp
            qed
          qed
          apply (rule conjI)
          subgoal
          proof -
            show "\<forall>x. (?f x = [] \<longleftrightarrow> [y\<leftarrow>ys @ ys'. fst y = x] = []) \<and>
              (?f x \<noteq> [] \<longrightarrow> last (?f x) = last [y\<leftarrow>ys @ ys'. fst y = x])"
              (is "\<forall>x. ?P x \<and> ?Q x")
            proof
              fix x
              have "?P x"
              proof
                assume "?f x = []"
                hence "[y\<leftarrow>?x @ ys''. fst y = x] = []"
                  using O by simp
                moreover from this have "[y\<leftarrow>?xs @ ys'. fst y = x] = []"
                  using J and K by simp
                ultimately show "[y\<leftarrow>ys @ ys'. fst y = x] = []"
                  using H by simp
              next
                assume "[y\<leftarrow>ys @ ys'. fst y = x] = []"
                hence "[y\<leftarrow>?x @ ?xs @ ys'. fst y = x] = []"
                  using H by simp
                moreover from this have "[y\<leftarrow>ys''. fst y = x] = []"
                  using J and K by simp
                ultimately show "?f x = []"
                  using O by simp
              qed
              moreover have "?Q x"
              proof (clarify, cases "[y\<leftarrow>ys''. fst y = x]")
                case Nil
                hence "last (?f x) = last [y\<leftarrow>?x. fst y = x]"
                  using O by simp
                moreover have "[y\<leftarrow>?xs @ ys'. fst y = x] = []"
                  using J and K and Nil by simp
                hence
                 "last [y\<leftarrow>ys @ ys'. fst y = x] = last [y\<leftarrow>?x. fst y = x]"
                  using H by simp
                ultimately show
                 "last (?f x) = last [y\<leftarrow>ys @ ys'. fst y = x]"
                  by simp
              next
                case Cons
                hence "last (?f x) = last (f x)"
                  using K and O by simp
                moreover have R: "f x \<noteq> []"
                  using K and Cons by simp
                hence "last [y\<leftarrow>?xs @ ys'. fst y = x] = last (f x)"
                  using J by simp
                moreover have "[y\<leftarrow>?xs @ ys'. fst y = x] \<noteq> []"
                  using J and R by simp
                ultimately show
                 "last (?f x) = last [y\<leftarrow>ys @ ys'. fst y = x]"
                  using H by simp
              qed
              ultimately show "?P x \<and> ?Q x" ..
            qed
          qed
          by (rule conjI, rule exI [of _ "concat (map fst ?ws)"],
           insert M Q, auto simp only: ctyping1_merge_def)
      qed
    qed
  qed
qed

lemma ctyping1_merge_append_idem_fst:
  assumes
    A: "\<And>ys ys'. ys \<in> \<turnstile> c\<^sub>1 \<Longrightarrow> ys' \<in> \<turnstile> c\<^sub>1 \<Longrightarrow>
      ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>1)" and
    B: "\<And>ys ys'. ys \<in> \<turnstile> c\<^sub>2 \<Longrightarrow> ys' \<in> \<turnstile> c\<^sub>2 \<Longrightarrow>
      ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>2)" and
    C: "s \<in> A" and
    D: "ys \<in> \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2" and
    E: "ys' \<in> \<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2"
  shows "ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>1 \<squnion>\<^sub>@ \<turnstile> c\<^sub>2)"
  apply (subst ctyping1_merge_append_def)
  apply (split if_split)
  apply (rule conjI)
  subgoal
  proof
    assume F: "card (\<turnstile> c\<^sub>2) = Suc 0"
    with D obtain ys\<^sub>1 and ys\<^sub>2 where
      G: "ys = ys\<^sub>1 @ ys\<^sub>2" and
      H: "ys\<^sub>1 \<in> \<turnstile> c\<^sub>1" and
      I: "ys\<^sub>2 \<in> \<turnstile> c\<^sub>2"
      by (auto simp: ctyping1_merge_append_def ctyping1_append_def)
    from E and F obtain ys\<^sub>1' and ys\<^sub>2' where
      J: "ys' = ys\<^sub>1' @ ys\<^sub>2'" and
      K: "ys\<^sub>1' \<in> \<turnstile> c\<^sub>1" and
      L: "ys\<^sub>2' \<in> \<turnstile> c\<^sub>2"
      by (auto simp: ctyping1_merge_append_def ctyping1_append_def)
    have M: "ys\<^sub>2' = ys\<^sub>2"
      using F and I and L by (fastforce simp: card_1_singleton_iff)
    obtain f and s' and t'' and ys\<^sub>1'' where
      N: "ctyping1_idem_lhs s t t' ys\<^sub>1 ys\<^sub>1' =
        ctyping1_idem_rhs f s' t''" and
      O: "\<forall>x. (f x = [] \<longleftrightarrow> [y\<leftarrow>ys\<^sub>1 @ ys\<^sub>1'. fst y = x] = []) \<and>
        (f x \<noteq> [] \<longrightarrow> last (f x) = last [y\<leftarrow>ys\<^sub>1 @ ys\<^sub>1'. fst y = x])" and
      P: "f = (\<lambda>x. [y\<leftarrow>ys\<^sub>1''. fst y = x])" and
      Q: "ys\<^sub>1'' \<in> \<turnstile> c\<^sub>1" and
      R: "s' \<in> A"
      using A [OF H K] by auto
    let ?f = "\<lambda>x. [y\<leftarrow>ys\<^sub>1'' @ ys\<^sub>2. fst y = x]"
    let ?t = "\<lambda>x. if [y\<leftarrow>ys\<^sub>2. fst y = x] = [] then t'' x else t' x"
    show "ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>1 @ \<turnstile> c\<^sub>2)"
      apply (rule exI [of _ ?f])
      apply (rule exI [of _ s'])
      apply (rule conjI)
       apply (rule exI [of _ ?t])
       apply (rule ext)
      subgoal for x
      proof (cases "[y\<leftarrow>ys\<^sub>2. fst y = x]", cases "f x = []")
        case Nil
        moreover case True
        ultimately have "s x = s' x"
          using O by (insert fun_cong [OF N, of x], simp)
        moreover have "[y\<leftarrow>ys'. fst y = x] = []"
          using J and M and O and Nil and True by simp
        moreover have "[y\<leftarrow>ys. fst y = x] = []"
          using G and O and Nil and True by simp
        moreover have "?f x = []"
          using P and Nil and True by simp
        ultimately show "ctyping1_idem_lhs s t t' ys ys' x =
          ctyping1_idem_rhs ?f s' ?t x"
          by simp
      next
        case Nil
        moreover from this have
         "[y\<leftarrow>ys'. fst y = x] = [y\<leftarrow>ys\<^sub>1'. fst y = x]"
          using J and M by simp
        moreover have "[y\<leftarrow>ys. fst y = x] = [y\<leftarrow>ys\<^sub>1. fst y = x]"
          using G and Nil by simp
        moreover case False
        moreover from this have "?f x \<noteq> []"
          using P by simp
        moreover have "last (?f x) = last (f x)"
          using P and Nil by simp
        ultimately show "ctyping1_idem_lhs s t t' ys ys' x =
          ctyping1_idem_rhs ?f s' ?t x"
          by (insert fun_cong [OF N, of x], auto)
      next
        case Cons
        moreover from this have "[y\<leftarrow>ys'. fst y = x] \<noteq> []"
          using J and M by simp
        moreover have
         "last [y\<leftarrow>ys'. fst y = x] = last [y\<leftarrow>ys\<^sub>2. fst y = x]"
          using J and M and Cons by simp
        ultimately show "ctyping1_idem_lhs s t t' ys ys' x =
          ctyping1_idem_rhs ?f s' ?t x"
          by simp
      qed
      apply (rule conjI)
      subgoal
      proof -
        show "\<forall>x. (?f x = [] \<longleftrightarrow> [y\<leftarrow>ys @ ys'. fst y = x] = []) \<and>
          (?f x \<noteq> [] \<longrightarrow> last (?f x) = last [y\<leftarrow>ys @ ys'. fst y = x])"
          (is "\<forall>x. ?P x \<and> ?Q x")
        proof
          fix x
          have "?P x"
            using G and J and M and O and P by auto
          moreover have "?Q x"
          proof (clarify, cases "[y\<leftarrow>ys\<^sub>2. fst y = x]")
            case Nil
            moreover assume "?f x \<noteq> []"
            ultimately have
             "last (?f x) = last [y\<leftarrow>ys\<^sub>1 @ ys\<^sub>1'. fst y = x]"
              using O and P by simp
            thus "last (?f x) = last [y\<leftarrow>ys @ ys'. fst y = x]"
              using G and J and M and Nil by simp
          next
            case Cons
            thus "last (?f x) = last [y\<leftarrow>ys @ ys'. fst y = x]"
              using J and M by simp
          qed
          ultimately show "?P x \<and> ?Q x" ..
        qed
      qed
      by (rule conjI, rule exI [of _ "ys\<^sub>1'' @ ys\<^sub>2"],
       insert I Q R, auto simp: ctyping1_append_def)
  qed
  subgoal
  proof
    assume F: "card (\<turnstile> c\<^sub>2) \<noteq> Suc 0"
    with D obtain ws and xs where
      G: "ys = ws @ xs" and
      H: "ws \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2" and
      I: "xs \<in> \<turnstile> c\<^sub>2"
      by (auto simp: ctyping1_merge_append_def ctyping1_append_def)
    from E and F obtain ws' and xs' where
      J: "ys' = ws' @ xs'" and
      K: "ws' \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2" and
      L: "xs' \<in> \<turnstile> c\<^sub>2"
      by (auto simp: ctyping1_merge_append_def ctyping1_append_def)
    from I have "[(xs, False)] \<in> \<turnstile> c\<^sub>1 \<Squnion> \<turnstile> c\<^sub>2" ..
    hence M: "xs \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2"
      by (force simp: ctyping1_merge_def)
    obtain f and s' and r and zs where
      N: "ctyping1_idem_lhs s t t' ws xs =
        ctyping1_idem_rhs f s' r" and
      O: "\<forall>x. (f x = [] \<longleftrightarrow> [y\<leftarrow>ws @ xs. fst y = x] = []) \<and>
        (f x \<noteq> [] \<longrightarrow> last (f x) = last [y\<leftarrow>ws @ xs. fst y = x])" and
      P: "f = (\<lambda>x. [y\<leftarrow>zs. fst y = x])" and
      Q: "zs \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2" and
      R: "s' \<in> A"
      using ctyping1_merge_idem_fst [OF A B C H M] by auto
    obtain f' and s'' and r' and zs' where
      S: "ctyping1_idem_lhs s t t' zs ws' =
        ctyping1_idem_rhs f' s'' r'" and
      T: "\<forall>x. (f' x = [] \<longleftrightarrow> [y\<leftarrow>zs @ ws'. fst y = x] = []) \<and>
        (f' x \<noteq> [] \<longrightarrow> last (f' x) = last [y\<leftarrow>zs @ ws'. fst y = x])" and
      U: "f' = (\<lambda>x. [y\<leftarrow>zs'. fst y = x])" and
      V: "zs' \<in> \<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2" and
      W: "s'' \<in> A"
      using ctyping1_merge_idem_fst [OF A B C Q K] by auto
    let ?f = "\<lambda>x. [y\<leftarrow>zs' @ xs'. fst y = x]"
    let ?t = "\<lambda>x. if [y\<leftarrow>xs'. fst y = x] = [] then r' x else t' x"
    show "ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>1 \<squnion> \<turnstile> c\<^sub>2 @ \<turnstile> c\<^sub>2)"
      apply (rule exI [of _ ?f])
      apply (rule exI [of _ s''])
      apply (rule conjI)
       apply (rule exI [of _ ?t])
       apply (rule ext)
      subgoal for x
      proof (cases "[y\<leftarrow>xs'. fst y = x]", cases "f' x = []")
        case Nil
        moreover case True
        hence "s x = s'' x"
          using T by (insert fun_cong [OF S, of x], simp)
        moreover have "[y\<leftarrow>ys'. fst y = x] = []"
          using J and T and Nil and True by simp
        moreover have "[y\<leftarrow>zs. fst y = x] = []"
          using T and True by simp
        hence "[y\<leftarrow>ys. fst y = x] = []"
          using G and O and P by simp
        moreover have "?f x = []"
          using U and Nil and True by simp
        ultimately show "ctyping1_idem_lhs s t t' ys ys' x =
          ctyping1_idem_rhs ?f s'' ?t x"
          by simp
      next
        case Nil
        moreover from this have
          X: "[y\<leftarrow>ys'. fst y = x] = [y\<leftarrow>ws'. fst y = x]"
          using J by simp
        moreover case False
        moreover have
         "[y\<leftarrow>zs. fst y = x] \<noteq> [] \<and> [y\<leftarrow>ys. fst y = x] \<noteq> [] \<and>
            last [y\<leftarrow>ys. fst y = x] = last [y\<leftarrow>zs. fst y = x]"
          (is "?P \<and> ?Q \<and> ?R") if
          a: "[y\<leftarrow>ys'. fst y = x] = []"
        proof -
          have ?P
            using T and X and False and a by simp
          moreover from this have ?Q
            using G and O and P by simp
          moreover have ?R
            using G and O and P and `?P` by simp
          ultimately show ?thesis
            by simp
        qed
        moreover have "?f x \<noteq> []"
          using U and False by simp
        moreover have "last (?f x) = last (f' x)"
          using U and Nil by simp
        ultimately show "ctyping1_idem_lhs s t t' ys ys' x =
          ctyping1_idem_rhs ?f s'' ?t x"
          by (insert fun_cong [OF S, of x], auto)
      next
        case Cons
        moreover from this have "[y\<leftarrow>ys'. fst y = x] \<noteq> []"
          using J by simp
        moreover have
         "last [y\<leftarrow>ys'. fst y = x] = last [y\<leftarrow>xs'. fst y = x]"
          using J and Cons by simp
        ultimately show "ctyping1_idem_lhs s t t' ys ys' x =
          ctyping1_idem_rhs ?f s'' ?t x"
          by simp
      qed
      apply (rule conjI)
      subgoal
      proof -
        show "\<forall>x. (?f x = [] \<longleftrightarrow> [y\<leftarrow>ys @ ys'. fst y = x] = []) \<and>
          (?f x \<noteq> [] \<longrightarrow> last (?f x) = last [y\<leftarrow>ys @ ys'. fst y = x])"
          (is "\<forall>x. ?P x \<and> ?Q x")
        proof
          fix x
          have "?P x"
          proof
            assume "[y\<leftarrow>zs' @ xs'. fst y = x] = []"
            moreover from this have "[y\<leftarrow>zs @ ws'. fst y = x] = []"
              using T and U by simp
            moreover from this have "[y\<leftarrow>ws @ xs. fst y = x] = []"
              using O and P by simp
            ultimately show "[y\<leftarrow>ys @ ys'. fst y = x] = []"
              using G and J by simp
          next
            assume "[y\<leftarrow>ys @ ys'. fst y = x] = []"
            hence "[y\<leftarrow>ws @ xs @ ws' @ xs'. fst y = x] = []"
              using G and J by simp
            moreover from this have "[y\<leftarrow>zs. fst y = x] = []"
              using O and P by simp
            ultimately show "[y\<leftarrow>zs' @ xs'. fst y = x] = []"
              using T and U by simp
          qed
          moreover have "?Q x"
          proof (clarify, cases "[y\<leftarrow>xs'. fst y = x]")
            case Nil
            moreover assume "?f x \<noteq> []"
            ultimately have X: "f' x \<noteq> []"
              using U by simp
            hence Y: "last (?f x) = last [y\<leftarrow>zs @ ws'. fst y = x]"
              using T and U and Nil by simp
            show "last (?f x) = last [y\<leftarrow>ys @ ys'. fst y = x]"
            proof (cases "[y\<leftarrow>ws'. fst y = x] = []")
              case True
              moreover from this have "f x \<noteq> []"
                using P and T and X by simp
              ultimately have
               "last (?f x) = last [y\<leftarrow>ws @ xs. fst y = x]"
                using O and P and Y by simp
              thus ?thesis
                using G and J and Nil and True by simp
            next
              case False
              thus ?thesis
                using J and Y and Nil by simp
            qed
          qed (simp add: J)
          ultimately show "?P x \<and> ?Q x" ..
        qed
      qed
      by (rule conjI, rule exI [of _ "zs' @ xs'"],
       insert L V W, auto simp: ctyping1_append_def)
  qed
  done


lemma ctyping1_aux_idem_fst:
 "\<lbrakk>s \<in> A; ys \<in> \<turnstile> c; ys' \<in> \<turnstile> c\<rbrakk> \<Longrightarrow>
    ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c)"
proof (induction c arbitrary: ys ys')
  fix c\<^sub>1 c\<^sub>2 ys ys'
  show
   "\<lbrakk>\<And>ys ys'. s \<in> A \<Longrightarrow> ys \<in> \<turnstile> c\<^sub>1 \<Longrightarrow> ys' \<in> \<turnstile> c\<^sub>1 \<Longrightarrow>
      ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>1);
    \<And>ys ys'. s \<in> A \<Longrightarrow> ys \<in> \<turnstile> c\<^sub>2 \<Longrightarrow> ys' \<in> \<turnstile> c\<^sub>2 \<Longrightarrow>
      ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>2);
    s \<in> A; ys \<in> \<turnstile> c\<^sub>1;; c\<^sub>2; ys' \<in> \<turnstile> c\<^sub>1;; c\<^sub>2\<rbrakk> \<Longrightarrow>
      ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>1;; c\<^sub>2)"
    by (simp, rule ctyping1_merge_append_idem_fst [simplified])
next
  fix c\<^sub>1 c\<^sub>2 ys ys'
  show
   "\<lbrakk>\<And>ys ys'. s \<in> A \<Longrightarrow> ys \<in> \<turnstile> c\<^sub>1 \<Longrightarrow> ys' \<in> \<turnstile> c\<^sub>1 \<Longrightarrow>
      ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>1);
    \<And>ys ys'. s \<in> A \<Longrightarrow> ys \<in> \<turnstile> c\<^sub>2 \<Longrightarrow> ys' \<in> \<turnstile> c\<^sub>2 \<Longrightarrow>
      ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>2);
    s \<in> A; ys \<in> \<turnstile> c\<^sub>1 OR c\<^sub>2; ys' \<in> \<turnstile> c\<^sub>1 OR c\<^sub>2\<rbrakk> \<Longrightarrow>
      ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>1 OR c\<^sub>2)"
    by (simp, rule ctyping1_merge_idem_fst [simplified])
next
  fix b c\<^sub>1 c\<^sub>2 ys ys'
  assume
    A: "\<And>ys ys'. s \<in> A \<Longrightarrow> ys \<in> \<turnstile> c\<^sub>1 \<Longrightarrow> ys' \<in> \<turnstile> c\<^sub>1 \<Longrightarrow>
      ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>1)" and
    B: "\<And>ys ys'. s \<in> A \<Longrightarrow> ys \<in> \<turnstile> c\<^sub>2 \<Longrightarrow> ys' \<in> \<turnstile> c\<^sub>2 \<Longrightarrow>
      ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c\<^sub>2)" and
    C: "s \<in> A" and
    D: "ys \<in> \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2" and
    E: "ys' \<in> \<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2"
  show "ctyping1_idem_pred s t t' ys ys' A (\<turnstile> IF b THEN c\<^sub>1 ELSE c\<^sub>2)"
  proof (cases "\<turnstile> b")
    case None
    show ?thesis
      by (insert A B C D E None, simp,
       rule ctyping1_merge_idem_fst [simplified])
  next
    case (Some v)
    show ?thesis
    proof (cases v)
      case True
      thus ?thesis
        by (insert A C D E Some, simp add: ctyping1_merge_empty_rhs)
    next
      case False
      thus ?thesis
        by (insert B C D E Some, simp add: ctyping1_merge_empty_lhs)
    qed
  qed
next
  fix b c ys ys'
  assume
    A: "\<And>ys ys'. s \<in> A \<Longrightarrow> ys \<in> \<turnstile> c \<Longrightarrow> ys' \<in> \<turnstile> c \<Longrightarrow>
      ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c)" and
    B: "s \<in> A" and
    C: "ys \<in> \<turnstile> WHILE b DO c" and
    D: "ys' \<in> \<turnstile> WHILE b DO c"
  have E: "ctyping1_idem_pred s t t' ys ys' A (\<turnstile> WHILE b DO c)" if
    a: "ys \<in> \<turnstile> c" and
    b: "ys' \<in> \<turnstile> c" and
    c: "\<turnstile> b \<in> {Some True, None}"
  proof -
    have "ctyping1_idem_pred s t t' ys ys' A (\<turnstile> c)"
      using A and B and a and b by simp
    then obtain f and s' and t'' and ys'' where
      E: "ctyping1_idem_lhs s t t' ys ys' =
        ctyping1_idem_rhs f s' t''" and
      F: "\<forall>x. (f x = [] \<longleftrightarrow> [y\<leftarrow>ys @ ys'. fst y = x] = []) \<and>
        (f x \<noteq> [] \<longrightarrow> last (f x) = last [y\<leftarrow>ys @ ys'. fst y = x])" and
      G: "f = (\<lambda>x. [y\<leftarrow>ys''. fst y = x])" and
      H: "ys'' \<in> \<turnstile> c" and
      I: "s' \<in> A"
      by auto
    show ?thesis
      by (rule exI [of _ f], insert E F G H I c, force)
  qed
  show "ctyping1_idem_pred s t t' ys ys' A (\<turnstile> WHILE b DO c)"
  proof (cases "\<turnstile> b")
    case None
    show ?thesis
    proof (cases ys')
      case Nil
      show ?thesis
      proof (cases "ys = []")
        case True
        thus ?thesis
          by (insert B None Nil, force)
      next
        case False
        thus ?thesis
          by (insert B C None Nil, force)
      qed
    next
      case Cons
      show ?thesis
      proof (cases "ys = []")
        case True
        show ?thesis
          apply (insert B D None Cons True)
          apply (rule exI [of _ "\<lambda>x. [y\<leftarrow>ys'. fst y = x]"])
          apply (rule exI [of _ s])
          apply (rule conjI)
           apply fastforce
          apply (rule conjI)
           apply fastforce
          apply (rule conjI)
           apply (rule exI [of _ ys'])
          by simp_all
      next
        case False
        hence "ys \<in> \<turnstile> c \<and> ys' \<in> \<turnstile> c"
          using C and D and None and Cons by simp
        thus ?thesis
          using None by (blast intro: E)
      qed
    qed
  next
    case (Some v)
    show ?thesis
    proof (cases v)
      case True
      hence "ys \<in> \<turnstile> c \<and> ys' \<in> \<turnstile> c"
        using C and D and Some by simp
      thus ?thesis
        using Some and True by (fastforce intro: E)
    next
      case False
      hence "ys = [] \<and> ys' = []"
        using C and D and Some by simp
      thus ?thesis
        by (insert B Some False, simp)
    qed
  qed
qed fastforce+


lemma ctyping1_idem_fst_1:
 "\<lbrakk>s \<in> A; ys \<in> \<turnstile> c; ys' \<in> \<turnstile> c\<rbrakk> \<Longrightarrow> \<exists>f s'.
    (\<exists>t''. ctyping1_idem_lhs s t t' ys ys' = ctyping1_idem_rhs f s' t'') \<and>
    (\<exists>ys''. f = (\<lambda>x. [y\<leftarrow>ys''. fst y = x]) \<and> ys'' \<in> \<turnstile> c) \<and> s' \<in> A"
  apply (drule ctyping1_aux_idem_fst [where ys' = ys'], assumption+)
  apply clarify
  apply (rule exI, (rule conjI)?)+
   apply assumption
  by blast

lemma ctyping1_idem_fst_2:
 "\<lbrakk>s \<in> A; ys \<in> \<turnstile> c\<rbrakk> \<Longrightarrow> \<exists>f s'.
    (\<exists>t'.
      (\<lambda>x. if [y\<leftarrow>ys. fst y = x] = []
        then s x
        else case snd (last [y\<leftarrow>ys. fst y = x]) of None \<Rightarrow> t x | Some i \<Rightarrow> i) =
      (\<lambda>x. if f x = []
        then s' x
        else case snd (last (f x)) of None \<Rightarrow> t' x | Some i \<Rightarrow> i)) \<and>
    (\<exists>ys'. f = (\<lambda>x. [y\<leftarrow>ys'. fst y = x]) \<and> ys' \<in> \<turnstile> c) \<and>
    (\<exists>f' s''.
      (\<exists>t''. s' = (\<lambda>x. if f' x = []
        then s'' x
        else case snd (last (f' x)) of None \<Rightarrow> t'' x | Some i \<Rightarrow> i)) \<and>
      (\<exists>ys''. f' = (\<lambda>x. [y\<leftarrow>ys''. fst y = x]) \<and> ys'' \<in> \<turnstile> c) \<and> s'' \<in> A)"
  (is "\<lbrakk>_; _\<rbrakk> \<Longrightarrow> \<exists>_ _. (\<exists>_. ?f = _) \<and> _")
by (rule exI, rule exI [of _ ?f], fastforce)

lemma ctyping1_idem_fst:
 "\<turnstile> c (\<subseteq> A, X) = (B, Y) \<Longrightarrow> case \<turnstile> c (\<subseteq> B, Y) of (B', Y') \<Rightarrow> B' = B"
by (auto intro: ctyping1_idem_fst_1 ctyping1_idem_fst_2 simp: ctyping1_def)


lemma ctyping1_idem_snd_1:
  assumes
    A: "A \<noteq> {}" and
    B: "\<forall>r f s.
      (\<forall>t. r \<noteq> (\<lambda>x. if f x = [] then s x else case snd (last (f x)) of
        None \<Rightarrow> t x | Some i \<Rightarrow> i)) \<or>
      (\<forall>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<longrightarrow> ys \<notin> \<turnstile> c) \<or> s \<notin> A"
      (is "\<forall>r f s. (\<forall>t. r \<noteq> ?r f s t) \<or> _")
  shows "UNIV = S"
proof -
  obtain s where C: "s \<in> A"
    using A by blast
  obtain ys where D: "ys \<in> \<turnstile> c"
    by (insert ctyping1_aux_nonempty, blast)
  let ?f = "\<lambda>x. [y\<leftarrow>ys. fst y = x]"
  show ?thesis
    using B [rule_format, of "?r ?f s (\<lambda>x. 0)" ?f s] and C and D by auto
qed

lemma ctyping1_idem_snd_2:
 "{x. \<forall>f.
    (f x = [] \<longrightarrow> (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c) \<longrightarrow>
      (\<forall>f.
        (f x = [] \<longrightarrow> (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c) \<longrightarrow>
          x \<in> X) \<and>
        (f x \<noteq> [] \<longrightarrow> (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c) \<longrightarrow>
          (\<exists>i. snd (last (f x)) = Some i)))) \<and>
    (f x \<noteq> [] \<longrightarrow> (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c) \<longrightarrow>
      (\<exists>i. snd (last (f x)) = Some i))} =
  {x. \<forall>f.
    (f x = [] \<longrightarrow> (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c) \<longrightarrow>
      x \<in> X) \<and>
    (f x \<noteq> [] \<longrightarrow> (\<exists>ys. f = (\<lambda>x. [y\<leftarrow>ys. fst y = x]) \<and> ys \<in> \<turnstile> c) \<longrightarrow>
      (\<exists>i. snd (last (f x)) = Some i))}"
by (rule equalityI, force+)

lemma ctyping1_idem_snd:
 "\<turnstile> c (\<subseteq> A, X) = (B, Y) \<Longrightarrow> case \<turnstile> c (\<subseteq> B, Y) of (B', Y') \<Rightarrow> Y' = Y"
by (clarsimp simp: ctyping1_def ctyping1_idem_snd_1 ctyping1_idem_snd_2)


lemma ctyping1_idem:
 "\<turnstile> c (\<subseteq> A, X) = (B, Y) \<Longrightarrow> \<turnstile> c (\<subseteq> B, Y) = (B, Y)"
by (frule ctyping1_idem_fst, drule ctyping1_idem_snd, auto)

end

end
