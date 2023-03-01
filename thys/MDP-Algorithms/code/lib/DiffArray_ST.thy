(* Author: Peter Lammich *)

section \<open>Single Threaded Arrays\<close>
theory DiffArray_ST
imports DiffArray_Base
begin



subsection \<open>Primitive Operations\<close>

typedef 'a starray = "UNIV :: 'a array set" 
  morphisms Rep_starray STArray
  by blast
setup_lifting type_definition_starray

lift_definition starray_new :: "nat \<Rightarrow> 'a \<Rightarrow> 'a starray" is "array_new" .

lift_definition starray_tabulate :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a starray" is "array_tabulate" .
  
lift_definition starray_length :: "'a starray \<Rightarrow> nat" is array_length .
  
lift_definition starray_get :: "'a starray \<Rightarrow> nat \<Rightarrow> 'a" is array_get .

lift_definition starray_set :: "'a starray \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a starray" is array_set .
  
lift_definition starray_of_list :: "'a list \<Rightarrow> 'a starray" is \<open>array_of_list\<close> .

lift_definition starray_grow :: "'a starray \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a starray" is "array_grow" .

lift_definition starray_take :: "'a starray \<Rightarrow> nat \<Rightarrow> 'a starray" is array_take .

lift_definition starray_get_oo :: "'a \<Rightarrow> 'a starray \<Rightarrow> nat \<Rightarrow> 'a" is array_get_oo .

lift_definition starray_set_oo :: "(unit \<Rightarrow> 'a starray) \<Rightarrow> 'a starray \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a starray" is array_set_oo .

lift_definition starray_map :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a starray \<Rightarrow> 'b starray" is array_map .

lift_definition starray_fold :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a starray \<Rightarrow> 'b \<Rightarrow> 'b" is array_fold .

lift_definition starray_foldr :: "('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a starray \<Rightarrow> 'b \<Rightarrow> 'b" is array_foldr .


definition "starray_\<alpha> = array_\<alpha> o Rep_starray"  
 
subsubsection \<open>Refinement Lemmas\<close>

context
  notes [simp] = STArray_inverse array_eq_iff starray_\<alpha>_def
begin

  lemma starray_\<alpha>_inj: "starray_\<alpha> a = starray_\<alpha> b \<Longrightarrow> a=b" unfolding starray_\<alpha>_def by transfer auto

  lemma starray_eq_iff: "a=b \<longleftrightarrow> starray_\<alpha> a = starray_\<alpha> b" unfolding starray_\<alpha>_def by transfer auto
  
  lemma starray_new_refine[simp,array_refine]: "starray_\<alpha> (starray_new n a) = replicate n a" unfolding starray_\<alpha>_def by transfer auto

  lemma starray_tabulate_refine[simp,array_refine]: "starray_\<alpha> (starray_tabulate n f) = tabulate n f" unfolding starray_\<alpha>_def by transfer auto
  
  lemma starray_length_refine[simp,array_refine]: "starray_length a = length (starray_\<alpha> a)" unfolding starray_\<alpha>_def by transfer auto
  
  lemma starray_get_refine[simp,array_refine]: "starray_get a i = starray_\<alpha> a ! i" unfolding starray_\<alpha>_def by transfer auto

  lemma starray_set_refine[simp,array_refine]: "starray_\<alpha> (starray_set a i x) = (starray_\<alpha> a)[i := x]" unfolding starray_\<alpha>_def by transfer auto

  lemma starray_of_list_refine[simp,array_refine]: "starray_\<alpha> (starray_of_list xs) = xs" unfolding starray_\<alpha>_def by transfer auto

  lemma starray_grow_refine[simp,array_refine]: 
    "starray_\<alpha> (starray_grow a n d) = take n (starray_\<alpha> a) @ replicate (n-length (starray_\<alpha> a)) d"
    unfolding starray_\<alpha>_def by transfer auto

  lemma starray_take_refine[simp,array_refine]: "starray_\<alpha> (starray_take a n) = take n (starray_\<alpha> a)"
    unfolding starray_\<alpha>_def by transfer auto
  
  lemma starray_get_oo_refine[simp,array_refine]: "starray_get_oo x a i = (if i<length (starray_\<alpha> a) then starray_\<alpha> a!i else x)" unfolding starray_\<alpha>_def by transfer auto

  lemma starray_set_oo_refine[simp,array_refine]: "starray_\<alpha> (starray_set_oo f a i x) 
    = (if i<length (starray_\<alpha> a) then (starray_\<alpha> a)[i:=x] else starray_\<alpha> (f ()))" 
    unfolding starray_\<alpha>_def by transfer auto

  lemma starray_map_refine[simp,array_refine]: "starray_\<alpha> (starray_map f a) = map f (starray_\<alpha> a)"
    unfolding starray_\<alpha>_def by transfer auto

  lemma starray_fold_refine[simp, array_refine]: "starray_fold f a s = fold f (starray_\<alpha> a) s"  
    unfolding starray_\<alpha>_def by transfer auto
    
  lemma starray_foldr_refine[simp, array_refine]: "starray_foldr f a s = foldr f (starray_\<alpha> a) s"  
    unfolding starray_\<alpha>_def by transfer auto
    
              
end  

lifting_update starray.lifting
lifting_forget starray.lifting

subsection \<open>Code Generator Setup\<close>

subsubsection \<open>Code-Numeral Preparation\<close>


definition [code del]: "starray_new' == starray_new o nat_of_integer"
definition [code del]: "starray_tabulate' n f \<equiv> starray_tabulate (nat_of_integer n) (f o integer_of_nat)"

definition [code del]: "starray_length' == integer_of_nat o starray_length"
definition [code del]: "starray_get' a == starray_get a o nat_of_integer"
definition [code del]: "starray_set' a == starray_set a o nat_of_integer"
definition [code del]:
  "starray_get_oo' x a == starray_get_oo x a o nat_of_integer"
definition [code del]:
  "starray_set_oo' f a == starray_set_oo f a o nat_of_integer"


lemma [code]:
  "starray_new == starray_new' o integer_of_nat"
  "starray_tabulate n f == starray_tabulate' (integer_of_nat n) (f o nat_of_integer)"
  "starray_length == nat_of_integer o starray_length'"
  "starray_get a == starray_get' a o integer_of_nat"
  "starray_set a == starray_set' a o integer_of_nat"
  "starray_get_oo x a == starray_get_oo' x a o integer_of_nat"
  "starray_set_oo g a == starray_set_oo' g a o integer_of_nat"
  by (simp_all
    del: array_refine
    add: o_def
    add: starray_new'_def starray_tabulate'_def starray_length'_def starray_get'_def starray_set'_def
      starray_get_oo'_def starray_set_oo'_def)

text \<open>Fallbacks\<close>

lemmas starray_get_oo'_fallback[code] = starray_get_oo'_def[unfolded starray_get_oo_def[abs_def]]
lemmas starray_set_oo'_fallback[code] = starray_set_oo'_def[unfolded starray_set_oo_def[abs_def]]

lemma starray_tabulate'_fallback[code]: 
  "starray_tabulate' n f = starray_of_list (map (f o integer_of_nat) [0..<nat_of_integer n])"
  unfolding starray_tabulate'_def 
  by (simp add: starray_eq_iff tabulate_def)

lemma starray_new'_fallback[code]: "starray_new' n x = starray_of_list (replicate (nat_of_integer n) x)"  
  by (simp add: starray_new'_def starray_eq_iff)
  

(*
  Primitive operations, to be implemented for target:
  
    starray_of_list
    starray_tabulate' (dflt via of_list)
    starray_new' (dflt via of_list)

    starray_length'
    starray_get'
    starray_set'
    starray_get_oo' (dflt via array_get)

*)




code_printing code_module "STArray" \<rightharpoonup>
  (SML)
\<open>
structure STArray = struct

datatype 'a Cell = Invalid | Value of 'a array;

exception AccessedOldVersion;

type 'a starray = 'a Cell Unsynchronized.ref;

fun fromList l = Unsynchronized.ref (Value (Array.fromList l));
fun starray (size, v) = Unsynchronized.ref (Value (Array.array (size,v)));
fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
fun sub (Unsynchronized.ref Invalid, idx) = raise AccessedOldVersion |
    sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx);
fun update (aref,idx,v) =
  case aref of
    (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
    (Unsynchronized.ref (Value a)) => (
      aref := Invalid;
      Array.update (a,idx,v);
      Unsynchronized.ref (Value a)
    );

fun length (Unsynchronized.ref Invalid) = raise AccessedOldVersion |
    length (Unsynchronized.ref (Value a)) = Array.length a


structure IsabelleMapping = struct
type 'a ArrayType = 'a starray;

fun starray_new (n:IntInf.int) (a:'a) = starray (IntInf.toInt n, a);
fun starray_of_list (xs:'a list) = fromList xs;

fun starray_tabulate (n:IntInf.int) (f:IntInf.int -> 'a) = tabulate (IntInf.toInt n, f o IntInf.fromInt)

fun starray_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun starray_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun starray_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun starray_get_oo (d:'a) (a:'a ArrayType) (i:IntInf.int) =
  sub (a,IntInf.toInt i) handle Subscript => d

fun starray_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:IntInf.int) (e:'a) =
  update (a, IntInf.toInt i, e) handle Subscript => d ()


end;

end;
\<close>


code_printing
  type_constructor starray \<rightharpoonup> (SML) "_/ STArray.IsabelleMapping.ArrayType"
| constant STArray \<rightharpoonup> (SML) "STArray.IsabelleMapping.starray'_of'_list"
| constant starray_new' \<rightharpoonup> (SML) "STArray.IsabelleMapping.starray'_new"
| constant starray_tabulate' \<rightharpoonup> (SML) "STArray.IsabelleMapping.starray'_tabulate"
| constant starray_length' \<rightharpoonup> (SML) "STArray.IsabelleMapping.starray'_length"
| constant starray_get' \<rightharpoonup> (SML) "STArray.IsabelleMapping.starray'_get"
| constant starray_set' \<rightharpoonup> (SML) "STArray.IsabelleMapping.starray'_set"
| constant starray_of_list \<rightharpoonup> (SML) "STArray.IsabelleMapping.starray'_of'_list"
| constant starray_get_oo' \<rightharpoonup> (SML) "STArray.IsabelleMapping.starray'_get'_oo"
| constant starray_set_oo' \<rightharpoonup> (SML) "STArray.IsabelleMapping.starray'_set'_oo"


subsection \<open>Tests\<close> 
(* TODO: Add more systematic tests! *)

definition "test1 \<equiv> 
  let a=starray_of_list [1,2,3,4,5,6];
      b=starray_tabulate 6 (Suc);
      a'=starray_set a 3 42;
      b'=starray_set b 3 42;
      c=starray_new 6 0
  in
    \<forall>i\<in>{0..<6}. 
      starray_get a' i = (if i=3 then 42 else i+1)  
    \<and> starray_get b' i = (if i=3 then 42 else i+1)  
    \<and> starray_get c i = (0::nat)
          "

lemma enum_rangeE:
  assumes "i\<in>{l..<h}"
  assumes "P l"
  assumes "i\<in>{Suc l..<h} \<Longrightarrow> P i"
  shows "P i"
  using assms
  by (metis atLeastLessThan_iff less_eq_Suc_le nat_less_le)          
          
          
lemma "test1"
  unfolding test1_def Let_def
  apply (intro ballI conjI)
  apply (erule enum_rangeE, (simp; fail))+ apply simp
  apply (erule enum_rangeE, (simp; fail))+ apply simp
  apply (erule enum_rangeE, (simp; fail))+ apply simp
  done  
  
ML_val \<open>
  if not @{code test1} then error "ERROR" else ()
\<close>          

export_code test1 checking OCaml? Haskell? SML


hide_const test1
hide_fact test1_def


experiment
begin

fun allTrue :: "bool list \<Rightarrow> nat \<Rightarrow> bool list" where
"allTrue a 0 = a" |
"allTrue a (Suc i) = (allTrue a i)[i := True]"

lemma length_allTrue: "n \<le> length a  \<Longrightarrow> length(allTrue a n) = length a"
by(induction n) (auto)

lemma "n \<le> length a \<Longrightarrow> \<forall>i < n. (allTrue a n) ! i"
by(induction n) (auto simp: nth_list_update length_allTrue)


fun allTrue' :: "bool array \<Rightarrow> nat \<Rightarrow> bool array" where
"allTrue' a 0 = a" |
"allTrue' a (Suc i) = array_set (allTrue' a i) i True"


lemma "array_\<alpha> (allTrue' xs i) = allTrue (array_\<alpha> xs) i"
  apply (induction xs i rule: allTrue'.induct)
  apply auto
  done


end



end
