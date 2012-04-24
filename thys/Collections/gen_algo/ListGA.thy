header {* \isaheader{Generic Algorithms for Sequences} *}
theory ListGA
imports 
  "../spec/ListSpec" 
  "../common/Misc"
begin

subsection {* Iterators *}

subsubsection {* iteratei (by get, size) *}
fun idx_iteratei_aux 
  :: "('s \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> ('\<sigma>\<Rightarrow>bool) \<Rightarrow> ('a \<Rightarrow>'\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
where
  "idx_iteratei_aux get sz i l c f \<sigma> = (
    if i=0 \<or> \<not> c \<sigma> then \<sigma>
    else idx_iteratei_aux get sz (i - 1) l c f (f (get l (sz-i)) \<sigma>)
  )"

declare idx_iteratei_aux.simps[simp del]

lemma idx_iteratei_aux_simps[simp]:
  "i=0 \<Longrightarrow> idx_iteratei_aux get sz i l c f \<sigma> = \<sigma>"
  "\<not>c \<sigma> \<Longrightarrow> idx_iteratei_aux get sz i l c f \<sigma> = \<sigma>"
  "\<lbrakk>i\<noteq>0; c \<sigma>\<rbrakk> \<Longrightarrow> idx_iteratei_aux get sz i l c f \<sigma> = idx_iteratei_aux get sz (i - 1) l c f (f (get l (sz-i)) \<sigma>)"
  apply -
  apply (subst idx_iteratei_aux.simps, simp)+
  done

definition "idx_iteratei get sz l c f \<sigma> == idx_iteratei_aux get (sz l) (sz l) l c f \<sigma>"

lemma idx_iteratei_eq_foldli:
  assumes "list_size \<alpha> invar sz"
  assumes "list_get \<alpha> invar get"
  assumes "invar s"
  shows "idx_iteratei get sz s = foldli (\<alpha> s)" 
proof -
  interpret list_size \<alpha> invar sz by fact
  interpret list_get \<alpha> invar get by fact

  {
    fix n l
    assume A: "Suc n \<le> length l"
    hence B: "length l - Suc n < length l" by simp
    from A have [simp]: "Suc (length l - Suc n) = length l - n" by simp
    from nth_drop'[OF B, simplified] have 
      "drop (length l - Suc n) l = l!(length l - Suc n)#drop (length l - n) l" 
      by simp
  } note drop_aux=this

  {
    fix s c f \<sigma> i
    assume "invar s" "i\<le>sz s"
    hence "idx_iteratei_aux get (sz s) i s c f \<sigma> = foldli (drop (sz s - i) (\<alpha> s)) c f \<sigma>"
    proof (induct i arbitrary: \<sigma>)
      case 0 with size_correct[of s] show ?case by simp
    next
      case (Suc n)
      note [simp, intro!] = Suc.prems(1)
      show ?case proof (cases "c \<sigma>")
        case False thus ?thesis by simp
      next
        case True[simp, intro!]
        show ?thesis using Suc by (simp add: get_correct size_correct drop_aux)
      qed
    qed
  } note aux=this

  show ?thesis
    unfolding idx_iteratei_def[abs_def]
    by (auto simp add: fun_eq_iff aux[OF `invar s`, of "sz s", simplified])
qed

lemma idx_iteratei_correct:
  assumes "list_size \<alpha> invar sz"
  assumes "list_get \<alpha> invar get"
  shows "list_iteratei \<alpha> invar (idx_iteratei get sz)"
using assms
unfolding list_iteratei_def
by (simp add: idx_iteratei_eq_foldli)


subsubsection {* reverse\_iteratei (by get, size) *}
fun idx_reverse_iteratei_aux 
  :: "('s \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 's \<Rightarrow> ('\<sigma>\<Rightarrow>bool) \<Rightarrow> ('a \<Rightarrow>'\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
where
  "idx_reverse_iteratei_aux get sz i l c f \<sigma> = (
    if i=0 \<or> \<not> c \<sigma> then \<sigma>
    else idx_reverse_iteratei_aux get sz (i - 1) l c f (f (get l (i - 1)) \<sigma>)
  )"

declare idx_reverse_iteratei_aux.simps[simp del]

lemma idx_reverse_iteratei_aux_simps[simp]:
  "i=0 \<Longrightarrow> idx_reverse_iteratei_aux get sz i l c f \<sigma> = \<sigma>"
  "\<not>c \<sigma> \<Longrightarrow> idx_reverse_iteratei_aux get sz i l c f \<sigma> = \<sigma>"
  "\<lbrakk>i\<noteq>0; c \<sigma>\<rbrakk> \<Longrightarrow> idx_reverse_iteratei_aux get sz i l c f \<sigma> = idx_reverse_iteratei_aux get sz (i - 1) l c f (f (get l (i - 1)) \<sigma>)"
  by (subst idx_reverse_iteratei_aux.simps, simp)+

definition "idx_reverse_iteratei get sz l c f \<sigma> == idx_reverse_iteratei_aux get (sz l) (sz l) l c f \<sigma>"

lemma idx_reverse_iteratei_eq_foldri:
  assumes "list_size \<alpha> invar sz"
  assumes "list_get \<alpha> invar get"
  assumes "invar s"
  shows "idx_reverse_iteratei get sz s = foldri (\<alpha> s)" 
proof -
  interpret list_size \<alpha> invar sz by fact
  interpret list_get \<alpha> invar get by fact

  {
    fix s c f \<sigma> i
    assume "invar s" "i\<le>sz s"
    hence "idx_reverse_iteratei_aux get (sz s) i s c f \<sigma> = foldri (take i (\<alpha> s)) c f \<sigma>"
    proof (induct i arbitrary: \<sigma>)
      case 0 with size_correct[of s] show ?case by simp
    next
      case (Suc n)
      note [simp, intro!] = Suc.prems(1)
      show ?case proof (cases "c \<sigma>")
        case False thus ?thesis by simp
      next
        case True[simp, intro!]
        show ?thesis using Suc 
          by (simp add: get_correct size_correct take_Suc_conv_app_nth)
      qed
    qed
  } note aux=this

  show ?thesis
    unfolding idx_reverse_iteratei_def[abs_def]
    apply (simp add: fun_eq_iff aux[OF `invar s`, of "sz s", simplified])
    apply (simp add: size_correct[OF `invar s`])
  done
qed

lemma idx_reverse_iteratei_correct:
  assumes "list_size \<alpha> invar sz"
  assumes "list_get \<alpha> invar get"
  shows "list_reverse_iteratei \<alpha> invar (idx_reverse_iteratei get sz)"
using assms
unfolding list_reverse_iteratei_def
by (simp add: idx_reverse_iteratei_eq_foldri)


subsection {* Size (by iterator) *}
definition it_size :: "('s \<Rightarrow> ('x,nat) set_iterator) \<Rightarrow> 's \<Rightarrow> nat"
  where "it_size iti l == iti l (\<lambda>_. True) (\<lambda>x res. Suc res) (0::nat)"

lemma it_size_correct:
  assumes "list_iteratei \<alpha> invar it"
  shows "list_size \<alpha> invar (it_size it)"
proof -
  interpret list_iteratei \<alpha> invar it by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold it_size_def)
    apply (simp add: iteratei_correct foldli_foldl)
    done
qed

subsubsection {* By reverse\_iterator *}
lemma it_size_correct_rev:
  assumes "list_reverse_iteratei \<alpha> invar it"
  shows "list_size \<alpha> invar (it_size it)"
proof -
  interpret list_reverse_iteratei \<alpha> invar it by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold it_size_def)
    apply (simp add: reverse_iteratei_correct foldri_foldr)
    done
qed

subsection {* Get (by iteratori) *}
definition iti_get:: "('s \<Rightarrow> ('x,nat \<times> 'x option) set_iterator) \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> 'x" 
  where "iti_get iti s i = 
    the (snd (iti s
              (\<lambda>(i,x). x=None) 
              (\<lambda>x (i,_). if i=0 then (0,Some x) else (i - 1,None)) 
              (i,None)))"

lemma iti_get_correct:
  assumes iti_OK: "list_iteratei \<alpha> invar iti"
  shows "list_get \<alpha> invar (iti_get iti)"
proof 
  fix s i 
  assume "invar s" "i < length (\<alpha> s)"
 
  from list_iteratei.iteratei_correct[OF iti_OK, OF `invar s`]
  have iti_s_eq: "iti s = foldli (\<alpha> s)" by simp

  def l \<equiv> "\<alpha> s"
  from `i < length (\<alpha> s)`
  show "iti_get iti s i = \<alpha> s ! i"
    unfolding iti_get_def iti_s_eq l_def[symmetric]
  proof (induct i arbitrary: l)
    case 0
    then obtain x xs where l_eq[simp]: "l = x # xs" by (cases l, auto)
    thus ?case by simp
  next
    case (Suc i)
    note ind_hyp = Suc(1)
    note Suc_i_le = Suc(2)
    from Suc_i_le obtain x xs where l_eq[simp]: "l = x # xs" by (cases l, auto)
    
    from ind_hyp [of xs] Suc_i_le
    show ?case by simp
  qed
qed


end

