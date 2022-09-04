theory BPlusTree_Imp
  imports
    BPlusTree
    Partially_Filled_Array
    Basic_Assn
    Inst_Ex_Assn
begin

lemma butlast_double_Cons: "butlast (x#y#xs) = x#(butlast (y#xs))"
  by auto

lemma last_double_Cons: "last (x#y#xs) = (last (y#xs))"
  by auto

section "Imperative B-tree Definition"

text "The heap data type definition. Anything stored on the heap always contains data,
leafs are represented as None."

(* Option as we need a default for non-initializeed entries *)
datatype 'a btnode =
  Btleaf "'a pfarray" "'a btnode ref option" |
  Btnode "('a btnode ref option *'a) pfarray" "'a btnode ref"


text \<open>Selector Functions\<close>
primrec kvs :: "'a::heap btnode \<Rightarrow> ('a btnode ref option * 'a) pfarray" where
  [sep_dflt_simps]: "kvs (Btnode ts _) = ts"

primrec lst :: "'a::heap btnode \<Rightarrow> 'a btnode ref" where
  [sep_dflt_simps]: "lst (Btnode _ t) = t"

primrec vals :: "'a::heap btnode \<Rightarrow> 'a pfarray" where
  [sep_dflt_simps]: "vals (Btleaf ts _) = ts"

primrec fwd :: "'a::heap btnode \<Rightarrow> 'a btnode ref option" where
  [sep_dflt_simps]: "fwd (Btleaf _ t) = t"

text \<open>Encoding to natural numbers, as required by Imperative/HOL\<close>
  (* Note: should also work using the package "Deriving" *)
fun
  btnode_encode :: "'a::heap btnode \<Rightarrow> nat"
  where
    "btnode_encode (Btnode ts t) = to_nat (Some ts, Some t, None::'a pfarray option, None::'a btnode ref option option)" |
    "btnode_encode (Btleaf ts t) = to_nat (None::('a btnode ref option * 'a) pfarray option, None::'a btnode ref option, Some ts, Some t)"

instance btnode :: (heap) heap
  apply (rule heap_class.intro)
   apply (rule countable_classI [of "btnode_encode"])
  apply(elim btnode_encode.elims)
  apply auto
  ..

text "The refinement relationship to abstract B-trees."

text "The idea is: a refines the given node of degree k where the first leaf node of the subtree
of a is r and the forward pointer in the last leaf node is z"

find_theorems list_assn
find_theorems id_assn

fun bplustree_assn :: "nat \<Rightarrow> ('a::heap) bplustree \<Rightarrow> 'a btnode ref \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option \<Rightarrow> assn" where
  "bplustree_assn k (Leaf xs) a r z = 
 (\<exists>\<^sub>A xsi fwd.
      a \<mapsto>\<^sub>r Btleaf xsi fwd
    * is_pfa (2*k) xs xsi
    * \<up>(fwd = z)
    * \<up>(r = Some a)
  )" |
  "bplustree_assn k (Node ts t) a r z = 
 (\<exists>\<^sub>A tsi ti tsi' tsi'' rs.
      a \<mapsto>\<^sub>r Btnode tsi ti
    * bplustree_assn k t ti (last (r#rs)) (last (rs@[z]))
    * is_pfa (2*k) tsi' tsi
    * \<up>(length tsi' = length rs)
    * \<up>(tsi'' = zip (zip (map fst tsi') (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi'))
    * list_assn ((\<lambda> t (ti,r',z'). bplustree_assn k t (the ti) r' z') \<times>\<^sub>a id_assn) ts tsi''
    )"


find_theorems "map _ (zip _ _)"
(*
rs = the list of pointers to the leaves of this subtree
TODO how to weave rs@[z] and a#rs into the list_assn most elegantly
*)

text "With the current definition of deletion, we would
also need to directly reason on nodes and not only on references
to them."

fun btnode_assn :: "nat \<Rightarrow> ('a::heap) bplustree \<Rightarrow> 'a btnode \<Rightarrow> 'a btnode ref option \<Rightarrow> 'a btnode ref option \<Rightarrow> assn" where
  "btnode_assn k (Leaf xs) (Btleaf xsi zi) r z = 
 (\<exists>\<^sub>A xsi zi.
    is_pfa (2*k) xs xsi
    * \<up>(zi = z)
  )" |
  "btnode_assn k (Node ts t) (Btnode tsi ti) r z = 
 (\<exists>\<^sub>A tsi' tsi'' rs.
    bplustree_assn k t ti (last (r#rs)) (last (rs@[z]))
    * is_pfa (2*k) tsi' tsi
    * \<up>(length tsi' = length rs)
    * \<up>(tsi'' = zip (zip (map fst tsi') (zip (butlast (r#rs)) (butlast (rs@[z])))) (map snd tsi'))
    * list_assn ((\<lambda> t (ti,r',z'). bplustree_assn k t (the ti) r' z') \<times>\<^sub>a id_assn) ts tsi''
    )" |
  "btnode_assn _ _ _ _ _ = false"

abbreviation "blist_assn k ts tsi'' \<equiv> list_assn ((\<lambda> t (ti,r',z'). bplustree_assn k t (the ti) r' z') \<times>\<^sub>a id_assn) ts tsi'' "

end