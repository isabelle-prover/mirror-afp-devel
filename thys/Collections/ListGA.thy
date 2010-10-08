header {* \isaheader{Generic Algorithms for Sequences} *}
theory ListGA
imports ListSpec "common/Misc"
begin

subsection {* Iterators *}

subsubsection {* iteratei (by get, size) *}
fun idx_iteratei_aux 
  :: "('s \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('\<sigma>\<Rightarrow>bool) \<Rightarrow> ('a \<Rightarrow>'\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> 's \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
where
  "idx_iteratei_aux get sz i c f l \<sigma> = (
    if i=0 \<or> \<not> c \<sigma> then \<sigma>
    else idx_iteratei_aux get sz (i - 1) c f l (f (get l (sz-i)) \<sigma>)
  )"

declare idx_iteratei_aux.simps[simp del]

lemma idx_iteratei_aux_simps[simp]:
  "i=0 \<Longrightarrow> idx_iteratei_aux get sz i c f l \<sigma> = \<sigma>"
  "\<not>c \<sigma> \<Longrightarrow> idx_iteratei_aux get sz i c f l \<sigma> = \<sigma>"
  "\<lbrakk>i\<noteq>0; c \<sigma>\<rbrakk> \<Longrightarrow> idx_iteratei_aux get sz i c f l \<sigma> = idx_iteratei_aux get sz (i - 1) c f l (f (get l (sz-i)) \<sigma>)"
  apply -
  apply (subst idx_iteratei_aux.simps, simp)+
  done


definition "idx_iteratei get sz c f l \<sigma> == idx_iteratei_aux get (sz l) (sz l) c f l \<sigma>"


lemma idx_iteratei_correct:
  assumes "list_size \<alpha> invar sz"
  assumes "list_get \<alpha> invar get"
  shows "list_iteratei \<alpha> invar (idx_iteratei get sz)"
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
    hence "idx_iteratei_aux get (sz s) i c f s \<sigma> = foldli c f (drop (sz s - i) (\<alpha> s)) \<sigma>"
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
    apply (unfold_locales)
    apply (unfold idx_iteratei_def)
  proof -
    fix s c f \<sigma>
    assume INV: "invar s"
    from aux[OF INV, of "sz s", simplified] show
      "idx_iteratei_aux get (sz s) (sz s) c f s \<sigma> = foldli c f (\<alpha> s) \<sigma>" .
  qed
qed

subsubsection {* reverse\_iteratei (by get, size) *}
fun idx_reverse_iteratei_aux 
  :: "('s \<Rightarrow> nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('\<sigma>\<Rightarrow>bool) \<Rightarrow> ('a \<Rightarrow>'\<sigma> \<Rightarrow> '\<sigma>) \<Rightarrow> 's \<Rightarrow> '\<sigma> \<Rightarrow> '\<sigma>"
where
  "idx_reverse_iteratei_aux get sz i c f l \<sigma> = (
    if i=0 \<or> \<not> c \<sigma> then \<sigma>
    else idx_reverse_iteratei_aux get sz (i - 1) c f l (f (get l (i - 1)) \<sigma>)
  )"

declare idx_reverse_iteratei_aux.simps[simp del]

lemma idx_reverse_iteratei_aux_simps[simp]:
  "i=0 \<Longrightarrow> idx_reverse_iteratei_aux get sz i c f l \<sigma> = \<sigma>"
  "\<not>c \<sigma> \<Longrightarrow> idx_reverse_iteratei_aux get sz i c f l \<sigma> = \<sigma>"
  "\<lbrakk>i\<noteq>0; c \<sigma>\<rbrakk> \<Longrightarrow> idx_reverse_iteratei_aux get sz i c f l \<sigma> = idx_reverse_iteratei_aux get sz (i - 1) c f l (f (get l (i - 1)) \<sigma>)"
  apply -
  apply (subst idx_reverse_iteratei_aux.simps, simp)+
  done


definition "idx_reverse_iteratei get sz c f l \<sigma> == idx_reverse_iteratei_aux get (sz l) (sz l) c f l \<sigma>"


lemma idx_reverse_iteratei_correct:
  assumes "list_size \<alpha> invar sz"
  assumes "list_get \<alpha> invar get"
  shows "list_reverse_iteratei \<alpha> invar (idx_reverse_iteratei get sz)"
proof -
  interpret list_size \<alpha> invar sz by fact
  interpret list_get \<alpha> invar get by fact

  {
    fix s c f \<sigma> i
    assume "invar s" "i\<le>sz s"
    hence "idx_reverse_iteratei_aux get (sz s) i c f s \<sigma> = foldri c f (take i (\<alpha> s)) \<sigma>"
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
    apply (unfold_locales)
    apply (unfold idx_reverse_iteratei_def)
  proof -
    fix s c f \<sigma>
    assume INV: "invar s"
    from aux[OF INV, of "sz s", simplified] show
      "idx_reverse_iteratei_aux get (sz s) (sz s) c f s \<sigma> = foldri c f (\<alpha> s) \<sigma>" 
      by (simp add: size_correct INV)
  qed
qed

subsubsection {* iterate (by iteratei) *}
  definition iti_iterate :: "('s,'x,'\<sigma>) list_iteratori \<Rightarrow> ('s,'x,'\<sigma>) list_iterator"
  where "iti_iterate it == it (\<lambda>x. True)"

  lemma (in list_iteratei) iti_iterate_correct:
    "list_iterate \<alpha> invar (iti_iterate iteratei)"
    apply (unfold_locales)
    apply (unfold iti_iterate_def)
    apply (simp add: iteratei_correct foldli_foldl)
    done

subsubsection {* reverse\_iterate (by reverse\_iteratei) *}
  definition riti_reverse_iterate :: "('s,'x,'\<sigma>) list_iteratori \<Rightarrow> ('s,'x,'\<sigma>) list_iterator"
  where "riti_reverse_iterate it == it (\<lambda>x. True)"

  lemma (in list_reverse_iteratei) riti_reverse_iterate_correct:
    "list_reverse_iterate \<alpha> invar (riti_reverse_iterate reverse_iteratei)"
    apply (unfold_locales)
    apply (unfold riti_reverse_iterate_def)
    apply (simp add: reverse_iteratei_correct foldri_foldr)
    done

subsection {* Size (by iterator) *}
definition it_size :: "('s,'x,nat) list_iterator \<Rightarrow> 's \<Rightarrow> nat"
  where "it_size it l == it (\<lambda>x res. Suc res) l (0::nat)"


lemma it_size_correct:
  assumes "list_iterate \<alpha> invar it"
  shows "list_size \<alpha> invar (it_size it)"
proof -
  interpret list_iterate \<alpha> invar it by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold it_size_def)
    apply (simp add: iterate_correct)
    done
qed

subsubsection {* By reverse\_iterator *}
lemma it_size_correct_rev:
  assumes "list_reverse_iterate \<alpha> invar it"
  shows "list_size \<alpha> invar (it_size it)"
proof -
  interpret list_reverse_iterate \<alpha> invar it by fact
  show ?thesis
    apply (unfold_locales)
    apply (unfold it_size_def)
    apply (simp add: reverse_iterate_correct)
    done
qed

subsection {* Get (by iteratori) *}
definition iti_get:: "('s,'x,nat \<times> 'x option) list_iteratori \<Rightarrow> 's \<Rightarrow> nat \<Rightarrow> 'x" 
  where "iti_get it s i = 
    the (snd (it 
              (\<lambda>(i,x). x=None) 
              (\<lambda>x (i,_). if i=0 then (0,Some x) else (i - 1,None)) 
              s 
              (i,None)))"

lemma iti_get_correct:
  assumes "list_iteratei \<alpha> invar it"
  shows "list_get \<alpha> invar (iti_get it)"
proof -
  interpret list_iteratei \<alpha> invar it by fact
  show ?thesis
    apply unfold_locales
    apply (unfold iti_get_def)
    apply (simp add: iteratei_correct)
    apply (rule_tac I="\<lambda>l1 l2 (i',x). (case x of None \<Rightarrow> i\<ge>length l1 \<and> i'=i - length l1 | Some xx \<Rightarrow> xx=\<alpha> s ! i)" in foldli_rule_P)
    apply simp
    apply (case_tac \<sigma>)
    apply simp
    apply auto
    apply (auto split: option.split_asm)
    done
qed


end

