(*  Title:      Imperative_HOL_Time/Array_Time.thy
    Author:     Maximilian P. L. Haslbeck & Bohua Zhan, TU Muenchen
*)
section \<open>Monadic arrays\<close>

text \<open>This theory is an adaptation of \<open>HOL/Imperative_HOL/Array.thy\<close>,
 adding time bookkeeping.\<close>

theory Array_Time
imports Heap_Time_Monad
begin       

subsection \<open>Primitives\<close>

definition present :: "heap \<Rightarrow> 'a::heap array \<Rightarrow> bool" where
  "present h a \<longleftrightarrow> addr_of_array a < lim h"

definition get :: "heap \<Rightarrow> 'a::heap array \<Rightarrow> 'a list" where
  "get h a = map from_nat (arrays h (TYPEREP('a)) (addr_of_array a))"

definition set :: "'a::heap array \<Rightarrow> 'a list \<Rightarrow> heap \<Rightarrow> heap" where
  "set a x = arrays_update (\<lambda>h. h(TYPEREP('a) := ((h(TYPEREP('a))) (addr_of_array a:=map to_nat x))))"

definition alloc :: "'a list \<Rightarrow> heap \<Rightarrow> 'a::heap array \<times> heap" where
  "alloc xs h = (let
     l = lim h;
     r = Array l;
     h'' = set r xs (h\<lparr>lim := l + 1\<rparr>)
   in (r, h''))"

definition length :: "heap \<Rightarrow> 'a::heap array \<Rightarrow> nat" where
  "length h a = List.length (get h a)"
  
definition update :: "'a::heap array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> heap \<Rightarrow> heap" where
  "update a i x h = set a ((get h a)[i:=x]) h"

definition noteq :: "'a::heap array \<Rightarrow> 'b::heap array \<Rightarrow> bool" (infix "=!!=" 70) where
  "r =!!= s \<longleftrightarrow> TYPEREP('a) \<noteq> TYPEREP('b) \<or> addr_of_array r \<noteq> addr_of_array s"


subsection \<open>Monad operations\<close>

definition new :: "nat \<Rightarrow> 'a::heap \<Rightarrow> 'a array Heap" where
  [code del]: "new n x = Heap_Time_Monad.heap (%h. let (r,h') = alloc (replicate n x) h in (r,h',n+1))"

definition of_list :: "'a::heap list \<Rightarrow> 'a array Heap" where
  [code del]: "of_list xs = Heap_Time_Monad.heap (%h. let (r,h') = alloc xs h in (r,h',1+List.length xs))"

definition make :: "nat \<Rightarrow> (nat \<Rightarrow> 'a::heap) \<Rightarrow> 'a array Heap" where
  [code del]: "make n f = Heap_Time_Monad.heap (%h. let (r,h') = alloc (map f [0 ..< n]) h in (r,h',n+1))"

definition len :: "'a::heap array \<Rightarrow> nat Heap" where
  [code del]: "len a = Heap_Time_Monad.tap (\<lambda>h. length h a)"

definition nth :: "'a::heap array \<Rightarrow> nat \<Rightarrow> 'a Heap" where
  [code del]: "nth a i = Heap_Time_Monad.guard (\<lambda>h. i < length h a)
    (\<lambda>h. (get h a ! i, h, 1))"

definition upd :: "nat \<Rightarrow> 'a \<Rightarrow> 'a::heap array \<Rightarrow> 'a::heap array Heap" where
  [code del]: "upd i x a = Heap_Time_Monad.guard (\<lambda>h. i < length h a)
    (\<lambda>h. (a, update a i x h, 1))"

definition map_entry :: "nat \<Rightarrow> ('a::heap \<Rightarrow> 'a) \<Rightarrow> 'a array \<Rightarrow> 'a array Heap" where
  [code del]: "map_entry i f a = Heap_Time_Monad.guard (\<lambda>h. i < length h a)
    (\<lambda>h. (a, update a i (f (get h a ! i)) h, 2))"

definition swap :: "nat \<Rightarrow> 'a \<Rightarrow> 'a::heap array \<Rightarrow> 'a Heap" where
  [code del]: "swap i x a = Heap_Time_Monad.guard (\<lambda>h. i < length h a)
    (\<lambda>h. (get h a ! i, update a i x h, 2 ))"  (* questionable *)

definition freeze :: "'a::heap array \<Rightarrow> 'a list Heap" where
  [code del]: "freeze a = Heap_Time_Monad.heap (\<lambda>h. (get h a, h, 1+length h a)) "


subsection \<open>Properties\<close>

text \<open>FIXME: Does there exist a "canonical" array axiomatisation in
the literature?\<close>

text \<open>Primitives\<close>

lemma noteq_sym: "a =!!= b \<Longrightarrow> b =!!= a"
  and unequal [simp]: "a \<noteq> a' \<longleftrightarrow> a =!!= a'"
  unfolding noteq_def by auto

lemma noteq_irrefl: "r =!!= r \<Longrightarrow> False"
  unfolding noteq_def by auto

lemma present_alloc_noteq: "present h a \<Longrightarrow> a =!!= fst (alloc xs h)"
  by (simp add: present_def noteq_def alloc_def Let_def)

lemma get_set_eq [simp]: "get (set r x h) r = x"
  by (simp add: get_def set_def o_def)

lemma get_set_neq [simp]: "r =!!= s \<Longrightarrow> get (set s x h) r = get h r"
  by (simp add: noteq_def get_def set_def)

lemma set_same [simp]:
  "set r x (set r y h) = set r x h"
  by (simp add: set_def)

lemma set_set_swap:
  "r =!!= r' \<Longrightarrow> set r x (set r' x' h) = set r' x' (set r x h)"
  by (simp add: Let_def fun_eq_iff noteq_def set_def)

lemma get_update_eq [simp]:
  "get (update a i v h) a = (get h a) [i := v]"
  by (simp add: update_def)

lemma nth_update_neq [simp]:
  "a =!!= b \<Longrightarrow> get (update b j v h) a ! i = get h a ! i"
  by (simp add: update_def noteq_def)

lemma get_update_elem_neqIndex [simp]:
  "i \<noteq> j \<Longrightarrow> get (update a j v h) a ! i = get h a ! i"
  by simp

lemma length_update [simp]: 
  "length (update b i v h) = length h"
  by (simp add: update_def length_def set_def get_def fun_eq_iff)

lemma update_swap_neq:
  "a =!!= a' \<Longrightarrow> 
  update a i v (update a' i' v' h) 
  = update a' i' v' (update a i v h)"
apply (unfold update_def)
apply simp
apply (subst set_set_swap, assumption)
apply (subst get_set_neq)
apply (erule noteq_sym)
apply simp
done

lemma update_swap_neqIndex:
  "\<lbrakk> i \<noteq> i' \<rbrakk> \<Longrightarrow> update a i v (update a i' v' h) = update a i' v' (update a i v h)"
  by (auto simp add: update_def set_set_swap list_update_swap)

lemma get_alloc:
  "get (snd (alloc xs h)) (fst (alloc ys h)) = xs"
  by (simp add: Let_def split_def alloc_def)

lemma length_alloc:
  "length (snd (alloc (xs :: 'a::heap list) h)) (fst (alloc (ys :: 'a list) h)) = List.length xs"
  by (simp add: Array_Time.length_def get_alloc)

lemma set:
  "set (fst (alloc ls h))
     new_ls (snd (alloc ls h))
       = snd (alloc new_ls h)"
  by (simp add: Let_def split_def alloc_def)

lemma present_update [simp]: 
  "present (update b i v h) = present h"
  by (simp add: update_def present_def set_def get_def fun_eq_iff)

lemma present_alloc [simp]:
  "present (snd (alloc xs h)) (fst (alloc xs h))"
  by (simp add: present_def alloc_def set_def Let_def)

lemma not_present_alloc [simp]:
  "\<not> present h (fst (alloc xs h))"
  by (simp add: present_def alloc_def Let_def)


text \<open>Monad operations\<close>

lemma execute_new [execute_simps]:
  "execute (new n x) h = Some (let (r,h') = alloc (replicate n x) h in (r,h',n+1))"
  by (simp add: new_def execute_simps)

lemma success_newI [success_intros]:
  "success (new n x) h"
  by (auto intro: success_intros simp add: new_def)

lemma effect_newI [effect_intros]:
  assumes "(a, h') = alloc (replicate n x) h"
  shows "effect (new n x) h h' a (n+1)"
  apply (rule effectI) apply (simp add: assms execute_simps)  by (metis assms case_prod_conv) 
    
lemma effect_newE [effect_elims]:
  assumes "effect (new n x) h h' r n'"
  obtains "r = fst (alloc (replicate n x) h)" "h' = snd (alloc (replicate n x) h)" 
    "get h' r = replicate n x" "present h' r" "\<not> present h r" "n+1=n'"
  using assms apply (rule effectE) using  case_prod_beta get_alloc execute_new
  by (metis (mono_tags, lifting) fst_conv not_present_alloc option.sel present_alloc sndI) 
  
  (* apply (si mp add: case_prod_beta get_alloc execute_simps) refactor proof *) 

lemma execute_of_list [execute_simps]:
  "execute (of_list xs) h = Some (let (r,h') = alloc xs h in (r,h',1 + List.length xs))"
  by (simp add: of_list_def execute_simps)

lemma success_of_listI [success_intros]:
  "success (of_list xs) h"
  by (auto intro: success_intros simp add: of_list_def)

lemma effect_of_listI [effect_intros]:
  assumes "(a, h') = alloc xs h"
  shows "effect (of_list xs) h h' a (1 + List.length xs)"
  by (rule effectI, simp add: assms execute_simps, metis assms case_prod_conv) 
    
    
lemma effect_of_listE [effect_elims]:
  assumes "effect (of_list xs) h h' r n'"
  obtains "r = fst (alloc xs h)" "h' = snd (alloc xs h)" 
    "get h' r = xs" "present h' r" "\<not> present h r" "n' = 1 + List.length xs"
  using assms apply (rule effectE) apply (simp add: get_alloc  execute_of_list) by (simp add: case_prod_unfold)

lemma execute_make [execute_simps]:
  "execute (make n f) h = Some (let (r,h') = alloc (map f [0 ..< n]) h in (r,h',n+1))"
  by (simp add: make_def execute_simps)

lemma success_makeI [success_intros]:
  "success (make n f) h"
  by (auto intro: success_intros simp add: make_def)

lemma effect_makeI [effect_intros]:
  assumes "(a, h') = alloc (map f [0 ..< n]) h"
  shows "effect (make n f) h h' a (n+1)"
  by (rule effectI) (simp add: assms execute_simps, metis assms case_prod_conv) 

lemma effect_makeE [effect_elims]:
  assumes "effect (make n f) h h' r n'"
  obtains "r = fst (alloc (map f [0 ..< n]) h)" "h' = snd (alloc (map f [0 ..< n]) h)" 
    "get h' r = map f [0 ..< n]" "present h' r" "\<not> present h r" "n+1=n'"
  using assms apply (rule effectE) using get_alloc  
  by (metis (mono_tags, opaque_lifting) effectE effect_makeI not_present_alloc present_alloc prod.collapse)
  
  (* apply (si mp add: get_alloc execute_make) by (s imp add: case_prod_unfold) *)

lemma execute_len [execute_simps]:
  "execute (len a) h = Some (length h a, h, 1)"
  by (simp add: len_def execute_simps)

lemma success_lenI [success_intros]:
  "success (len a) h"
  by (auto intro: success_intros simp add: len_def)

lemma effect_lengthI [effect_intros]:
  assumes "h' = h" "r = length h a" "n=1"
  shows "effect (len a) h h' r n"
  by (rule effectI) (simp add: assms execute_simps)

lemma effect_lengthE [effect_elims]:
  assumes "effect (len a) h h' r n"
  obtains "r = length h' a" "h' = h" "n=1" 
  using assms by (rule effectE) (simp add: execute_simps)

lemma execute_nth [execute_simps]:
  "i < length h a \<Longrightarrow>
    execute (nth a i) h = Some (get h a ! i, h,1)"
  "i \<ge> length h a \<Longrightarrow> execute (nth a i) h = None"
  by (simp_all add: nth_def execute_simps)

lemma success_nthI [success_intros]:
  "i < length h a \<Longrightarrow> success (nth a i) h"
  by (auto intro: success_intros simp add: nth_def)

lemma effect_nthI [effect_intros]:
  assumes "i < length h a" "h' = h" "r = get h a ! i" "n=1"
  shows "effect (nth a i) h h' r n"
  by (rule effectI) (insert assms, simp add: execute_simps)

lemma effect_nthE [effect_elims]:
  assumes "effect (nth a i) h h' r n"
  obtains "i < length h a" "r = get h a ! i" "h' = h" "n=1"
  using assms by (rule effectE) (cases "i < length h a", auto simp: execute_simps elim: successE)

lemma execute_upd [execute_simps]:
  "i < length h a \<Longrightarrow>
    execute (upd i x a) h = Some (a, update a i x h, 1)"
  "i \<ge> length h a \<Longrightarrow> execute (upd i x a) h = None"
  by (simp_all add: upd_def execute_simps)

lemma success_updI [success_intros]:
  "i < length h a \<Longrightarrow> success (upd i x a) h"
  by (auto intro: success_intros simp add: upd_def)

lemma effect_updI [effect_intros]:
  assumes "i < length h a" "h' = update a i v h" "n=1"
  shows "effect (upd i v a) h h' a n"
  by (rule effectI) (insert assms, simp add: execute_simps)

lemma effect_updE [effect_elims]:
  assumes "effect (upd i v a) h h' r n"
  obtains "r = a" "h' = update a i v h" "i < length h a" "n=1"
  using assms by (rule effectE) (cases "i < length h a", auto simp: execute_simps elim: successE)

lemma execute_map_entry [execute_simps]:
  "i < length h a \<Longrightarrow>
   execute (map_entry i f a) h =
      Some (a, update a i (f (get h a ! i)) h, 2)"
  "i \<ge> length h a \<Longrightarrow> execute (map_entry i f a) h = None"
  by (simp_all add: map_entry_def execute_simps)

lemma success_map_entryI [success_intros]:
  "i < length h a \<Longrightarrow> success (map_entry i f a) h"
  by (auto intro: success_intros simp add: map_entry_def)

lemma effect_map_entryI [effect_intros]:
  assumes "i < length h a" "h' = update a i (f (get h a ! i)) h" "r = a" "n=2"
  shows "effect (map_entry i f a) h h' r n"
  by (rule effectI) (insert assms, simp add: execute_simps)

lemma effect_map_entryE [effect_elims]:
  assumes "effect (map_entry i f a) h h' r n"
  obtains "r = a" "h' = update a i (f (get h a ! i)) h" "i < length h a" "n=2"
  using assms by (rule effectE) (cases "i < length h a", auto simp: execute_simps elim: successE)

lemma execute_swap [execute_simps]:
  "i < length h a \<Longrightarrow>
   execute (swap i x a) h =
      Some (get h a ! i, update a i x h, 2)"
  "i \<ge> length h a \<Longrightarrow> execute (swap i x a) h = None"
  by (simp_all add: swap_def execute_simps)

lemma success_swapI [success_intros]:
  "i < length h a \<Longrightarrow> success (swap i x a) h"
  by (auto intro: success_intros simp add: swap_def)

lemma effect_swapI [effect_intros]:
  assumes "i < length h a" "h' = update a i x h" "r = get h a ! i" "n=2"
  shows "effect (swap i x a) h h' r n"
  by (rule effectI) (insert assms, simp add: execute_simps)

lemma effect_swapE [effect_elims]:
  assumes "effect (swap i x a) h h' r n"
  obtains "r = get h a ! i" "h' = update a i x h" "i < length h a" "n=2"
  using assms by (rule effectE) (cases "i < length h a", auto simp: execute_simps elim: successE)

lemma execute_freeze [execute_simps]:
  "execute (freeze a) h = Some (get h a, h, 1+length h a)"
  by (simp add: freeze_def execute_simps)

lemma success_freezeI [success_intros]:
  "success (freeze a) h"
  by (auto intro: success_intros simp add: freeze_def)

lemma effect_freezeI [effect_intros]:
  assumes "h' = h" "r = get h a" "n=length h a"
  shows "effect (freeze a) h h' r (n+1)"
  by (rule effectI) (insert assms, simp add: execute_simps)

lemma effect_freezeE [effect_elims]:
  assumes "effect (freeze a) h h' r n"
  obtains "h' = h" "r = get h a" "n=length h a+1"
  using assms by (rule effectE) (simp add: execute_simps)

lemma upd_ureturn:
  "upd i x a \<then> ureturn a =   upd i x a "
  by (rule Heap_eqI) (simp add: bind_def guard_def upd_def execute_simps)

lemma array_make:
  "new n x = make n (\<lambda>_. x)"
  by (rule Heap_eqI) (simp add: map_replicate_trivial execute_simps)

lemma array_of_list_make [code]:
  "of_list xs = make (List.length xs) (\<lambda>n. xs ! n)"
  by (rule Heap_eqI) (simp add: map_nth execute_simps)

hide_const (open) present get set alloc length update noteq new of_list make len nth upd map_entry swap freeze


subsection \<open>Code generator setup\<close>

subsubsection \<open>Logical intermediate layer\<close>

definition new' where
  [code del]: "new' = Array_Time.new o nat_of_integer"

lemma [code]:
  "Array_Time.new = new' o of_nat"
  by (simp add: new'_def o_def)

definition make' where
  [code del]: "make' i f = Array_Time.make (nat_of_integer i) (f o of_nat)"

lemma [code]:
  "Array_Time.make n f = make' (of_nat n) (f o nat_of_integer)"
  by (simp add: make'_def o_def)

definition len' where
  [code del]: "len' a = Array_Time.len a \<bind> (\<lambda>n. ureturn (of_nat n))"

lemma [code]:
  "Array_Time.len a = len' a \<bind> (\<lambda>i. ureturn (nat_of_integer i))"
  by (simp add: len'_def execute_simps)    

definition nth' where
  [code del]: "nth' a = Array_Time.nth a o nat_of_integer"

lemma [code]:
  "Array_Time.nth a n = nth' a (of_nat n)"
  by (simp add: nth'_def)

definition upd' where
  [code del]: "upd' a i x = Array_Time.upd (nat_of_integer i) x a \<then> ureturn ()"

lemma [code]:
  "Array_Time.upd i x a = upd' a (of_nat i) x \<then> ureturn a"
  by (simp add: upd'_def upd_ureturn execute_simps)  

lemma [code]:
  "Array_Time.map_entry i f a = do {
     x \<leftarrow> Array_Time.nth a i;
     Array_Time.upd i (f x) a
   }"                                                                
  by (rule Heap_eqI) (simp add: bind_def guard_def map_entry_def execute_simps)

lemma [code]:
  "Array_Time.swap i x a = do {
     y \<leftarrow> Array_Time.nth a i;
     Array_Time.upd i x a;
     ureturn y
   }"
  by (rule Heap_eqI) (simp add: bind_def guard_def swap_def execute_simps)
(*
lemma [code]:
  "Array_Time.freeze a = do {
     n \<leftarrow> Array_Time.len a;
     Heap_Monad.fold_map (\<lambda>i. Array_Time.nth a i) [0..<n]
   }"
proof (rule Heap_eqI)
  fix h
  have *: "List.map
     (\<lambda>x. fst (the (if x < Array_Time.length h a
                    then Some (Array_Time.get h a ! x, h) else None)))
     [0..<Array_Time.length h a] =
       List.map (List.nth (Array_Time.get h a)) [0..<Array_Time.length h a]"
    by simp
  have "execute (Heap_Monad.fold_map (Array_Time.nth a) [0..<Array_Time.length h a]) h =
    Some (Array_Time.get h a, h)"
    apply (subst execute_fold_map_unchanged_heap)
    apply (simp_all add: nth_def guard_def * )
    apply (simp add: length_def map_nth)
    done
  then have "execute (do {
      n \<leftarrow> Array_Time.len a;
      Heap_Monad.fold_map (Array_Time.nth a) [0..<n]
    }) h = Some (Array_Time.get h a, h)"
    by (auto intro: execute_bind_eq_SomeI simp add: execute_simps)
  then show "execute (Array_Time.freeze a) h = execute (do {
      n \<leftarrow> Array_Time.len a;
      Heap_Monad.fold_map (Array_Time.nth a) [0..<n]
    }) h" by (simp add: execute_simps)
qed
*)
hide_const (open) new' make' len' nth' upd'


text \<open>SML\<close>

code_printing type_constructor array \<rightharpoonup> (SML) "_/ array"
code_printing constant Array \<rightharpoonup> (SML) "raise/ (Fail/ \"bare Array\")"
code_printing constant Array_Time.new' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.array/ ((_),/ (_)))"
code_printing constant Array_Time.of_list \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.fromList/ _)"
code_printing constant Array_Time.make' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.tabulate/ ((_),/ (_)))"
code_printing constant Array_Time.len' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.length/ _)"
code_printing constant Array_Time.nth' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.sub/ ((_),/ (_)))"
code_printing constant Array_Time.upd' \<rightharpoonup> (SML) "(fn/ ()/ =>/ Array.update/ ((_),/ (_),/ (_)))"
code_printing constant "HOL.equal :: 'a array \<Rightarrow> 'a array \<Rightarrow> bool" \<rightharpoonup> (SML) infixl 6 "="

code_reserved SML Array


text \<open>OCaml\<close>

code_printing type_constructor array \<rightharpoonup> (OCaml) "_/ array"
code_printing constant Array \<rightharpoonup> (OCaml) "failwith/ \"bare Array\""
code_printing constant Array_Time.new' \<rightharpoonup> (OCaml) "(fun/ ()/ ->/ Array.make/ (Big'_int.int'_of'_big'_int/ _)/ _)"
code_printing constant Array_Time.of_list \<rightharpoonup> (OCaml) "(fun/ ()/ ->/ Array.of'_list/ _)"
code_printing constant Array_Time.make' \<rightharpoonup> (OCaml)
  "(fun/ ()/ ->/ Array.init/ (Big'_int.int'_of'_big'_int/ _)/ (fun k'_ ->/ _/ (Big'_int.big'_int'_of'_int/ k'_)))"
code_printing constant Array_Time.len' \<rightharpoonup> (OCaml) "(fun/ ()/ ->/ Big'_int.big'_int'_of'_int/ (Array.length/ _))"
code_printing constant Array_Time.nth' \<rightharpoonup> (OCaml) "(fun/ ()/ ->/ Array.get/ _/ (Big'_int.int'_of'_big'_int/ _))"
code_printing constant Array_Time.upd' \<rightharpoonup> (OCaml) "(fun/ ()/ ->/ Array.set/ _/ (Big'_int.int'_of'_big'_int/ _)/ _)"
code_printing constant "HOL.equal :: 'a array \<Rightarrow> 'a array \<Rightarrow> bool" \<rightharpoonup> (OCaml) infixl 4 "="

code_reserved OCaml Array


text \<open>Haskell\<close>

code_printing type_constructor array \<rightharpoonup> (Haskell) "Heap.STArray/ Heap.RealWorld/ _"
code_printing constant Array \<rightharpoonup> (Haskell) "error/ \"bare Array\""
code_printing constant Array_Time.new' \<rightharpoonup> (Haskell) "Heap.newArray"
code_printing constant Array_Time.of_list \<rightharpoonup> (Haskell) "Heap.newListArray"
code_printing constant Array_Time.make' \<rightharpoonup> (Haskell) "Heap.newFunArray"
code_printing constant Array_Time.len' \<rightharpoonup> (Haskell) "Heap.lengthArray"
code_printing constant Array_Time.nth' \<rightharpoonup> (Haskell) "Heap.readArray"
code_printing constant Array_Time.upd' \<rightharpoonup> (Haskell) "Heap.writeArray"
code_printing constant "HOL.equal :: 'a array \<Rightarrow> 'a array \<Rightarrow> bool" \<rightharpoonup> (Haskell) infix 4 "=="
code_printing class_instance array :: HOL.equal \<rightharpoonup> (Haskell) -


text \<open>Scala\<close>

code_printing type_constructor array \<rightharpoonup> (Scala) "!Array.T[_]"
code_printing constant Array \<rightharpoonup> (Scala) "!sys.error(\"bare Array\")"
code_printing constant Array_Time.new' \<rightharpoonup> (Scala) "('_: Unit)/ => / Array.alloc((_))((_))"
code_printing constant Array_Time.make' \<rightharpoonup> (Scala) "('_: Unit)/ =>/ Array.make((_))((_))"
code_printing constant Array_Time.len' \<rightharpoonup> (Scala) "('_: Unit)/ =>/ Array.len((_))"
code_printing constant Array_Time.nth' \<rightharpoonup> (Scala) "('_: Unit)/ =>/ Array.nth((_), (_))"
code_printing constant Array_Time.upd' \<rightharpoonup> (Scala) "('_: Unit)/ =>/ Array.upd((_), (_), (_))"
code_printing constant Array_Time.freeze \<rightharpoonup> (Scala) "('_: Unit)/ =>/ Array.freeze((_))"
code_printing constant "HOL.equal :: 'a array \<Rightarrow> 'a array \<Rightarrow> bool" \<rightharpoonup> (Scala) infixl 5 "=="

end
