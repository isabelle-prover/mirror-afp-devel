(*  
    Title:      IArray_Addenda.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
    Maintainer: Jose Divasón <jose.divasonm at unirioja.es>
*)

section{*IArrays Addenda*}

theory IArray_Addenda
  imports 
  "$ISABELLE_HOME/src/HOL/Library/IArray"
begin

subsection{*Some previous instances*}

instantiation iarray :: (plus) plus
begin
definition plus_iarray :: "'a iarray \<Rightarrow> 'a iarray \<Rightarrow> 'a iarray"
  where "plus_iarray A B =  IArray.of_fun (\<lambda>n. A!!n + B !! n) (IArray.length A)"
instance proof qed
end

instantiation iarray :: (minus) minus
begin
definition minus_iarray :: "'a iarray \<Rightarrow> 'a iarray \<Rightarrow> 'a iarray"
  where "minus_iarray A B =  IArray.of_fun (\<lambda>n. A!!n - B !! n) (IArray.length A)"
instance proof qed
end

subsection{*Some previous definitions and properties for IArrays*}

subsubsection{*Lemmas*}

lemma of_fun_nth:
  assumes i: "i<n"
  shows "(IArray.of_fun f n) !! i = f i"
  unfolding IArray.of_fun_def using map_nth i by auto

subsubsection{*Definitions*}

fun all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a iarray \<Rightarrow> bool"
where "all p (IArray as) = (ALL a : set as. p a)"
 hide_const (open) all

fun exists :: "('a \<Rightarrow> bool) \<Rightarrow> 'a iarray \<Rightarrow> bool"
where "exists p (IArray as) = (EX a : set as. p a)"
hide_const (open) exists

(*
fun find :: "('a => bool) => 'a iarray => 'a option"
  where "find f (IArray as) = List.find f as"
hide_const (open) find

primrec findi_acc_list :: "(nat \<times> 'a => bool) => 'a list => nat => (nat \<times> 'a) option" where
  "findi_acc_list _ [] aux = None" |
  "findi_acc_list P (x#xs) aux = (if P (aux,x) then Some (aux,x) else findi_acc_list P xs (Suc aux))"

definition "findi_list P x = findi_acc_list P x 0"

fun findi :: "(nat \<times> 'a \<Rightarrow> bool) => 'a iarray => (nat \<times> 'a) option"
  where "findi f (IArray as) = findi_list f as"
hide_const (open) findi

fun foldl :: "(('a \<times> 'b) \<Rightarrow> 'b) => 'b => 'a iarray =>'b"
  where "foldl f a (IArray as) = List.foldl (\<lambda>x y. f (y,x)) a as"
hide_const (open) foldl

fun filter :: "('a \<Rightarrow> bool) => 'a iarray => 'a iarray"
  where "filter f (IArray as) = IArray (List.filter f as)"
hide_const (open) filter
*)

subsection{*Code generation*}

code_printing
 constant "IArray_Addenda.exists" \<rightharpoonup> (SML) "Vector.exists"
| constant "IArray_Addenda.all" \<rightharpoonup> (SML) "Vector.all"

(*
code_printing
  constant "IArray_Addenda.find"  \<rightharpoonup> (SML) "Vector.find"
| constant "IArray_Addenda.findi" \<rightharpoonup> (SML) "Vector.findi"
| constant "IArray_Addenda.foldl" \<rightharpoonup> (SML) "Vector.foldl"
*)

end
