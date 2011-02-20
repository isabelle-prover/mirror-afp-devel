(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header {* \isaheader{Indices of Sets} *}
theory SetIndex
imports "common/Misc" MapSpec SetSpec
begin
text_raw {*\label{thy:SetIndex}*}

text {*
  This theory defines an indexing operation that builds an index from a set 
  and an indexing function. 

  Here, index is a map from indices to all values of the set with that index.
  *}

subsection "Indexing by Function"

definition index :: "('a \<Rightarrow> 'i) \<Rightarrow> 'a set \<Rightarrow> 'i \<Rightarrow> 'a set"
  where "index f s i == { x\<in>s . f x = i }"

lemma indexI: "\<lbrakk> x\<in>s; f x = i \<rbrakk> \<Longrightarrow> x\<in>index f s i" by (unfold index_def) auto
lemma indexD: 
  "x\<in>index f s i \<Longrightarrow> x\<in>s"
  "x\<in>index f s i \<Longrightarrow> f x = i"
  by (unfold index_def) auto

lemma index_iff[simp]: "x\<in>index f s i \<longleftrightarrow> x\<in>s \<and> f x = i" by (simp add: index_def)
 
subsection "Indexing by Map"

definition index_map :: "('a \<Rightarrow> 'i) \<Rightarrow> 'a set \<Rightarrow> 'i \<rightharpoonup> 'a set"
  where "index_map f s i == let s=index f s i in if s={} then None else Some s"

definition im_\<alpha> where "im_\<alpha> im i == case im i of None \<Rightarrow> {} | Some s \<Rightarrow> s"

lemma index_map_correct: "im_\<alpha> (index_map f s) = index f s"
  apply (rule ext)
  apply (unfold index_def index_map_def im_\<alpha>_def)
  apply auto
  done

subsection "Indexing by Maps and Sets from the Isabelle Collections Framework"
text {*
  In this theory, we define the generic algorithm as constants outside any locale,
  but prove the correctness lemmas inside a locale that assumes correctness of all
  prerequisite functions.
  Finally, we export the correctness lemmas from the locale.
*}

-- "Lookup"
definition idx_lookup :: "_ \<Rightarrow> _ \<Rightarrow> 'i \<Rightarrow> 'm \<Rightarrow> 't" where
  "idx_lookup mlookup tempty i m == case mlookup i m of None \<Rightarrow> tempty | Some s \<Rightarrow> s"

locale index_env = 
  m: map_lookup m\<alpha> minvar mlookup +
  t: set_empty t\<alpha> tinvar tempty
  for m\<alpha> :: "'m \<Rightarrow> 'i \<rightharpoonup> 't" and minvar mlookup
  and t\<alpha> :: "'t \<Rightarrow> 'x set" and tinvar tempty
begin
  -- "Mapping indices to abstract indices"
  definition ci_\<alpha>' where
    "ci_\<alpha>' ci i == case m\<alpha> ci i of None \<Rightarrow> None | Some s \<Rightarrow> Some (t\<alpha> s)"

  definition "ci_\<alpha> == im_\<alpha> \<circ> ci_\<alpha>'"

  definition ci_invar where
    "ci_invar ci == minvar ci \<and> (\<forall>i s. m\<alpha> ci i = Some s \<longrightarrow> tinvar s)"

  lemma ci_impl_minvar: "ci_invar m \<Longrightarrow> minvar m" by (unfold ci_invar_def) auto

  definition is_index :: "('x \<Rightarrow> 'i) \<Rightarrow> 'x set \<Rightarrow> 'm \<Rightarrow> bool"
  where
    "is_index f s idx == ci_invar idx \<and> ci_\<alpha>' idx = index_map f s"

  lemma is_index_invar: "is_index f s idx \<Longrightarrow> ci_invar idx" 
    by (simp add: is_index_def)

  lemma is_index_correct: "is_index f s idx \<Longrightarrow> ci_\<alpha> idx = index f s"
    by (unfold is_index_def index_map_def ci_\<alpha>_def)
       (simp add: index_map_correct)

  abbreviation "lookup == idx_lookup mlookup tempty"

  lemma lookup_invar': "ci_invar m \<Longrightarrow> tinvar (lookup i m)"
    apply (unfold ci_invar_def idx_lookup_def)
    apply (auto split: option.split simp add: m.lookup_correct t.empty_correct)
    done

  lemma lookup_correct:
    assumes I[simp, intro!]: "is_index f s idx"
    shows 
      "t\<alpha> (lookup i idx) = index f s i"
      "tinvar (lookup i idx)"
  proof -
    case goal2 thus ?case using I by (simp add: is_index_def lookup_invar')
  next
    case goal1 
    have [simp, intro!]: "minvar idx" 
      using ci_impl_minvar[OF is_index_invar[OF I]] 
      by simp
    thus ?case 
    proof (cases "mlookup i idx")
      case None
      hence [simp]: "m\<alpha> idx i = None" by (simp add: m.lookup_correct)
      from is_index_correct[OF I] have "index f s i = ci_\<alpha> idx i" by simp
      also have "\<dots> = {}" by (simp add: ci_\<alpha>_def ci_\<alpha>'_def im_\<alpha>_def)
      finally show ?thesis by (simp add: idx_lookup_def None t.empty_correct)
    next
      case (Some si)
      hence [simp]: "m\<alpha> idx i = Some si" by (simp add: m.lookup_correct)
      from is_index_correct[OF I] have "index f s i = ci_\<alpha> idx i" by simp
      also have "\<dots> = t\<alpha> si" by (simp add: ci_\<alpha>_def ci_\<alpha>'_def im_\<alpha>_def)
      finally show ?thesis by (simp add: idx_lookup_def Some t.empty_correct)
    qed
  qed
end


  -- "Building indices"
definition idx_build_stepfun :: "
  ('i \<Rightarrow> 'm \<rightharpoonup> 't) \<Rightarrow> 
  ('i \<Rightarrow> 't \<Rightarrow> 'm \<Rightarrow> 'm) \<Rightarrow> 
  't \<Rightarrow> 
  ('x \<Rightarrow> 't \<Rightarrow> 't) \<Rightarrow> 
  ('x \<Rightarrow> 'i) \<Rightarrow> 'x \<Rightarrow> 'm \<Rightarrow> 'm" where
  "idx_build_stepfun mlookup mupdate tempty tinsert f x m == 
    let i=f x in
      (case mlookup i m of
        None \<Rightarrow> mupdate i (tinsert x tempty) m |
        Some s \<Rightarrow> mupdate i (tinsert x s) m
    )"

definition idx_build :: "
  'm \<Rightarrow>
  ('i \<Rightarrow> 'm \<rightharpoonup> 't) \<Rightarrow> 
  ('i \<Rightarrow> 't \<Rightarrow> 'm \<Rightarrow> 'm) \<Rightarrow> 
  't \<Rightarrow> 
  ('x \<Rightarrow> 't \<Rightarrow> 't) \<Rightarrow> 
  ('s,'x,'m) iterator \<Rightarrow>
  ('x \<Rightarrow> 'i) \<Rightarrow> 's \<Rightarrow> 'm" where
  "idx_build mempty mlookup mupdate tempty tinsert siterate f s 
   == siterate 
        (idx_build_stepfun mlookup mupdate tempty tinsert f) 
        s mempty"


locale idx_build_env = 
  index_env m\<alpha> minvar mlookup t\<alpha> tinvar tempty +
  m: map_empty m\<alpha> minvar mempty +
  m: map_update m\<alpha> minvar mupdate +
  t: set_ins t\<alpha> tinvar tinsert +
  s: set_iterate s\<alpha> sinvar siterate
  for m\<alpha> :: "'m \<Rightarrow> 'i \<rightharpoonup> 't" and minvar mempty mlookup mupdate
  and t\<alpha> :: "'t \<Rightarrow> 'x set" and tinvar tempty tinsert
  and s\<alpha> :: "'s \<Rightarrow> 'x set" and sinvar
  and siterate :: "('s,'x,'m) iterator"
begin

  abbreviation "idx_build_stepfun' == idx_build_stepfun mlookup mupdate tempty tinsert"
  abbreviation "idx_build' == 
    idx_build mempty mlookup mupdate tempty tinsert siterate"

  lemma idx_build_correct':
    assumes I: "sinvar s"
    shows "ci_\<alpha>' (idx_build' f s) = index_map f (s\<alpha> s)" (is ?T1) and
    [simp]: "ci_invar (idx_build' f s)" (is ?T2)
  proof -
    have "sinvar s \<Longrightarrow> 
      ci_\<alpha>' (idx_build' f s) = index_map f (s\<alpha> s) \<and> ci_invar (idx_build' f s)"
      apply (unfold idx_build_def)
      apply (rule_tac 
          I="\<lambda>it m. ci_\<alpha>' m = index_map f (s\<alpha> s - it) \<and> ci_invar m" 
          in iterate_rule_P)
      apply assumption
      apply (simp add: ci_invar_def m.empty_correct)
      apply (rule ext)
      apply (unfold ci_\<alpha>'_def index_map_def index_def)[1]
      apply (simp add: m.empty_correct)
      defer
      apply simp
      apply (rule conjI)
      defer
      apply (unfold idx_build_stepfun_def)[1]
      apply (auto 
        simp add: ci_invar_def m.update_correct m.lookup_correct 
                  t.empty_correct t.ins_correct Let_def 
        split: option.split) [1]
        
      apply (rule ext)
    proof -
      case (goal1 x it m i)
      hence INV[simp, intro!]: "minvar m" by (simp add: ci_invar_def)
      from goal1 have 
        INVS[simp, intro]: "!!q s. m\<alpha> m q = Some s \<Longrightarrow> tinvar s" 
        by (simp add: ci_invar_def)
      
      show ?case proof (cases "i=f x")
        case True[simp]
        show ?thesis proof (cases "m\<alpha> m (f x)")
          case None[simp]
          hence "idx_build_stepfun' f x m = mupdate i (tinsert x tempty) m"
            apply (unfold idx_build_stepfun_def) 
            apply (simp add: m.update_correct m.lookup_correct t.empty_correct)
            done
          hence "ci_\<alpha>' (idx_build_stepfun' f x m) i = Some {x}"
            by (simp add: m.update_correct 
                          t.ins_correct t.empty_correct ci_\<alpha>'_def)
          also {
            have "None = ci_\<alpha>' m (f x)" 
              by (simp add: ci_\<alpha>'_def)
            also from goal1(4) have "\<dots> = index_map f (s\<alpha> s - it) i" by simp
            finally have E: "{xa \<in> s\<alpha> s - it. f xa = i} = {}" 
              by (simp add: index_map_def index_def split: split_if_asm)
            moreover have 
              "{xa \<in> s\<alpha> s - (it - {x}). f xa = i} 
               = {xa \<in> s\<alpha> s - it. f xa = i} \<union> {x}"
              using goal1(2,3) by auto
            ultimately have "Some {x} = index_map f (s\<alpha> s - (it - {x})) i"
              by (unfold index_map_def index_def) auto
          } finally show ?thesis .
        next
          case (Some ss)[simp]
          hence [simp, intro!]: "tinvar ss" by (simp del: Some)
          hence "idx_build_stepfun' f x m = mupdate (f x) (tinsert x ss) m"
            by (unfold idx_build_stepfun_def) (simp add: m.update_correct m.lookup_correct)
          hence "ci_\<alpha>' (idx_build_stepfun' f x m) i = Some (insert x (t\<alpha> ss))"
            by (simp add: m.update_correct t.ins_correct ci_\<alpha>'_def)
          also {
              have "Some (t\<alpha> ss) = ci_\<alpha>' m (f x)" 
                by (simp add: ci_\<alpha>'_def)
            also from goal1(4) have "\<dots> = index_map f (s\<alpha> s - it) i" by simp
            finally have E: "{xa \<in> s\<alpha> s - it. f xa = i} = t\<alpha> ss" 
              by (simp add: index_map_def index_def split: split_if_asm)
            moreover have 
              "{xa \<in> s\<alpha> s - (it - {x}). f xa = i} 
               = {xa \<in> s\<alpha> s - it. f xa = i} \<union> {x}"
              using goal1(2,3) by auto
            ultimately have 
              "Some (insert x (t\<alpha> ss)) = index_map f (s\<alpha> s - (it - {x})) i"
              by (unfold index_map_def index_def) auto
          }
          finally show ?thesis .
        qed
      next
        case False hence C: "i\<noteq>f x" "f x\<noteq>i" by simp_all
        have "ci_\<alpha>' (idx_build_stepfun' f x m) i = ci_\<alpha>' m i"
          apply (unfold ci_\<alpha>'_def idx_build_stepfun_def)
          apply (simp 
            split: option.split_asm option.split 
            add: Let_def m.lookup_correct m.update_correct 
                 t.ins_correct t.empty_correct C)
          done
        also from goal1(4) have "ci_\<alpha>' m i = index_map f (s\<alpha> s - it) i" by simp
        also have 
          "{xa \<in> s\<alpha> s - (it - {x}). f xa = i} = {xa \<in> s\<alpha> s - it. f xa = i}"
          using goal1(2,3) C by auto
  hence "index_map f (s\<alpha> s - it) i = index_map f (s\<alpha> s - (it-{x})) i"
    by (unfold index_map_def index_def) simp
  finally show ?thesis .
      qed
    qed
    with I show ?T1 ?T2 by auto
  qed

  lemma idx_build_correct: 
    "sinvar s \<Longrightarrow> is_index f (s\<alpha> s) (idx_build' f s)"
    by (simp add: idx_build_correct' index_map_correct ci_\<alpha>_def is_index_def)

end

subsubsection "Exported Correctness Lemmas and Definitions"
text {*
  In order to allow simpler use, we 
  make the correctness lemmas visible outside the locale.
  We also export the @{const [source] index_env.is_index} predicate.
*}

definition idx_invar
  :: "('m \<Rightarrow> 'k \<rightharpoonup> 't) \<Rightarrow> ('m \<Rightarrow> bool) 
      \<Rightarrow> ('t \<Rightarrow> 'v set) \<Rightarrow> ('t \<Rightarrow> bool) 
      \<Rightarrow> ('v \<Rightarrow> 'k) \<Rightarrow> ('v set) \<Rightarrow> 'm \<Rightarrow> bool"
  where 
  "idx_invar m\<alpha> minvar t\<alpha> tinvar == index_env.is_index m\<alpha> minvar t\<alpha> tinvar"

lemma idx_build_correct:
  assumes "map_empty m\<alpha> minvar mempty"
  assumes "map_lookup m\<alpha> minvar mlookup"
  assumes "map_update m\<alpha> minvar mupdate"
  assumes "set_empty t\<alpha> tinvar tempty"
  assumes "set_ins t\<alpha> tinvar tinsert"
  assumes "set_iterate s\<alpha> sinvar siterate"

  constrains m\<alpha> :: "'m \<Rightarrow> 'i \<rightharpoonup> 't"
  constrains t\<alpha> :: "'t \<Rightarrow> 'x set"
  constrains s\<alpha> :: "'s \<Rightarrow> 'x set"
  constrains siterate :: "('s,'x,'m) iterator"

  assumes INV: "sinvar S"
  shows "idx_invar m\<alpha> minvar t\<alpha> tinvar f (s\<alpha> S) (idx_build mempty mlookup mupdate tempty tinsert siterate f S)"
proof -
  interpret m: map_empty m\<alpha> minvar mempty by fact
  interpret m: map_lookup m\<alpha> minvar mlookup by fact
  interpret m: map_update m\<alpha> minvar mupdate by fact
  interpret s: set_empty t\<alpha> tinvar tempty by fact
  interpret s: set_ins t\<alpha> tinvar tinsert by fact
  interpret t: set_iterate s\<alpha> sinvar siterate by fact

  interpret idx_build_env  
    m\<alpha> minvar mempty mlookup mupdate
    t\<alpha> tinvar tempty tinsert
    s\<alpha> sinvar siterate
    by unfold_locales
  from idx_build_correct[OF INV] show ?thesis
    by (unfold idx_invar_def idx_build_def)
qed

lemma idx_lookup_correct:
  assumes "map_lookup m\<alpha> minvar mlookup"
  assumes "set_empty t\<alpha> tinvar tempty"
  assumes INV: "idx_invar m\<alpha> minvar t\<alpha> tinvar f S idx"
  shows "t\<alpha> (idx_lookup mlookup tempty k idx) = index f S k" (is ?T1)
        "tinvar (idx_lookup mlookup tempty k idx)" (is ?T2)
proof -
  interpret m: map_lookup m\<alpha> minvar mlookup by fact
  interpret s: set_empty t\<alpha> tinvar tempty by fact
  
  interpret index_env 
    m\<alpha> minvar mlookup
    t\<alpha> tinvar tempty
    by unfold_locales

  from lookup_correct[OF INV[unfolded idx_invar_def], of k] show ?T1 ?T2
    by (simp_all add: idx_invar_def idx_lookup_def)
qed

end
