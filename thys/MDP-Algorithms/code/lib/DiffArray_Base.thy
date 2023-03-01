(* Author: Peter Lammich *)

theory DiffArray_Base
imports 
  Main
  "HOL-Library.Code_Target_Numeral"
  
begin


subsection \<open>Additional List Operations\<close>

definition "tabulate n f = map f [0..<n]"
  
context
  notes [simp] = tabulate_def
begin
  
lemma tabulate0[simp]: "tabulate 0 f = []" by simp

lemma tabulate_Suc: "tabulate (Suc n) f = tabulate n f @ [f n]" by simp

lemma tabulate_Suc': "tabulate (Suc n) f = f 0 # tabulate n (f o Suc)"
  by (simp add: map_upt_Suc del: upt_Suc)

lemma tabulate_const[simp]: "tabulate n (\<lambda>_. c) = replicate n c" by (auto simp: map_replicate_trivial)

lemma length_tabulate[simp]: "length (tabulate n f) = n" by simp
lemma nth_tabulate[simp]: "i<n \<Longrightarrow> tabulate n f ! i = f i" by simp 

lemma upd_tabulate: "(tabulate n f)[i:=x] = tabulate n (f(i:=x))" 
  apply (induction n)
  by (auto simp: list_update_append split: nat.split)

lemma take_tabulate: "take n (tabulate m f) = tabulate (min n m) f"
  by (simp add: min_def take_map)
  
lemma hd_tabulate[simp]: "n\<noteq>0 \<Longrightarrow> hd (tabulate n f) = f 0" 
  by (cases n) (simp add: map_upt_Suc del: upt_Suc)+
  
lemma tl_tabulate: "tl (tabulate n f) = tabulate (n-1) (f o Suc)"
  apply (simp add: map_upt_Suc map_Suc_upt del: upt_Suc flip: map_tl map_map)
  by (cases n; simp)

lemma tabulate_cong[fundef_cong]: "n=n' \<Longrightarrow> (\<And>i. i<n \<Longrightarrow> f i = f' i) \<Longrightarrow> tabulate n f = tabulate n' f'"
  by simp  

lemma tabulate_nth_take: "n \<le> length xs \<Longrightarrow> tabulate n ((!) xs) = take n xs"  
  by (rule nth_equalityI, auto)
  
end

lemma drop_tabulate: "drop n (tabulate m f) = tabulate (m-n) (f o (+)n)"
  apply (induction n arbitrary: m f)
  apply (auto simp: drop_Suc drop_tl tl_tabulate comp_def)
  done


subsection \<open>Primitive Operations\<close>

typedef 'a array = "UNIV :: 'a list set" 
  morphisms array_\<alpha> Array
  by blast
setup_lifting type_definition_array

lift_definition array_new :: "nat \<Rightarrow> 'a \<Rightarrow> 'a array" is "\<lambda>n a. replicate n a" .

lift_definition array_tabulate :: "nat \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'a array" is "\<lambda>n f. Array (tabulate n f)" .
  
lift_definition array_length :: "'a array \<Rightarrow> nat" is length .
  
lift_definition array_get :: "'a array \<Rightarrow> nat \<Rightarrow> 'a" is nth .

lift_definition array_set :: "'a array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array" is list_update .
  
lift_definition array_of_list :: "'a list \<Rightarrow> 'a array" is \<open>\<lambda>x. x\<close> .
  
 
subsubsection \<open>Refinement Lemmas\<close>

named_theorems array_refine
context
  notes [simp] = Array_inverse
begin

  lemma array_\<alpha>_inj: "array_\<alpha> a = array_\<alpha> b \<Longrightarrow> a=b" by transfer auto

  lemma array_eq_iff: "a=b \<longleftrightarrow> array_\<alpha> a = array_\<alpha> b" by transfer auto
  
  lemma array_new_refine[simp,array_refine]: "array_\<alpha> (array_new n a) = replicate n a" by transfer auto

  lemma array_tabulate_refine[simp,array_refine]: "array_\<alpha> (array_tabulate n f) = tabulate n f" by transfer auto
  
  lemma array_length_refine[simp,array_refine]: "array_length a = length (array_\<alpha> a)" by transfer auto
  
  lemma array_get_refine[simp,array_refine]: "array_get a i = array_\<alpha> a ! i" by transfer auto

  lemma array_set_refine[simp,array_refine]: "array_\<alpha> (array_set a i x) = (array_\<alpha> a)[i := x]" by transfer auto

  lemma array_of_list_refine[simp,array_refine]: "array_\<alpha> (array_of_list xs) = xs" by transfer auto
    
end  

lifting_update array.lifting
lifting_forget array.lifting

  
subsection \<open>Basic Derived Operations\<close>
text \<open>These operations may have direct implementations in target language\<close>

definition "array_grow a n dflt = (
  let la = array_length a in 
  array_tabulate n (\<lambda>i. if i<la then array_get a i else dflt)
)"

lemma tabulate_grow: "tabulate n (\<lambda>i. if i < length xs then xs!i else d) = take n xs @ (replicate (n-length xs) d)"
  apply (induction n)
  apply (auto simp: tabulate_Suc take_Suc_conv_app_nth replicate_append_same Suc_diff_le)
  done

lemma array_grow_refine[simp,array_refine]: 
  "array_\<alpha> (array_grow a n d) = take n (array_\<alpha> a) @ replicate (n-length (array_\<alpha> a)) d"
  by (auto simp: array_grow_def tabulate_grow cong: if_cong)

definition "array_take a n = (
  let n = min (array_length a) n in
  array_tabulate n (array_get a)
)"
  
lemma tabulate_take: "tabulate (min (length xs) n) ((!) xs) = take n xs"
  by (auto simp: min_def tabulate_nth_take)

lemma array_take_refine[simp,array_refine]: "array_\<alpha> (array_take a n) = take n (array_\<alpha> a)"
  by (auto simp: array_take_def tabulate_take cong: tabulate_cong)

text \<open>The following is a total version of
  \<open>array_get\<close>, which returns a default
  value in case the index is out of bounds.
  This can be efficiently implemented in the target language by catching
  exceptions.
\<close>
definition "array_get_oo x a i \<equiv>
  if i<array_length a then array_get a i else x"

lemma array_get_oo_refine[simp,array_refine]: "array_get_oo x a i = (if i<length (array_\<alpha> a) then array_\<alpha> a!i else x)"
  by (simp add: array_get_oo_def)

definition "array_set_oo f a i x \<equiv>
  if i<array_length a then array_set a i x else f()"

lemma array_set_oo_refine[simp,array_refine]: "array_\<alpha> (array_set_oo f a i x) 
  = (if i<length (array_\<alpha> a) then (array_\<alpha> a)[i:=x] else array_\<alpha> (f ()))"
  by (simp add: array_set_oo_def)
  
    
text \<open>
  Map array. No old versions for intermediate results need to be tracked, 
  which allows more efficient in-place implementation in case access to old 
  versions is forbidden.
\<close>
definition "array_map f a \<equiv> array_tabulate (array_length a) (f o array_get a)"
  
lemma array_map_refine[simp,array_refine]: "array_\<alpha> (array_map f a) = map f (array_\<alpha> a)"
  unfolding array_map_def
  apply (auto simp: tabulate_def simp flip: map_map cong: map_cong)
  by (smt (z3) atLeastLessThan_iff length_map map_eq_conv map_nth nth_map set_upt)

lemma array_map_cong[fundef_cong]: "a=a' \<Longrightarrow> (\<And>x. x\<in>set (array_\<alpha> a) \<Longrightarrow> f x = f' x) \<Longrightarrow> array_map f a = array_map f' a'" 
  by (simp add: array_eq_iff)


context
  fixes f :: "'a \<Rightarrow> 's \<Rightarrow> 's" and xs :: "'a list"
begin  
function foldl_idx where
  "foldl_idx i s = (if i<length xs then foldl_idx (i+1) (f (xs!i) s) else s)"  
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(i,_). length xs - i)")
  apply auto
  done
  
lemmas [simp del] = foldl_idx.simps  
  
lemma foldl_idx_eq: "foldl_idx i s = fold f (drop i xs) s"
  apply (induction i s rule: foldl_idx.induct)
  apply (subst foldl_idx.simps)
  apply (auto simp flip: Cons_nth_drop_Suc)
  done

lemma fold_by_idx: "fold f xs s = foldl_idx 0 s" using foldl_idx_eq by simp 
      
end  

fun foldr_idx where
  "foldr_idx f xs 0 s = s"
| "foldr_idx f xs (Suc i) s = foldr_idx f xs i (f (xs!i) s)"  

lemma foldr_idx_eq: "i\<le>length xs \<Longrightarrow> foldr_idx f xs i s = foldr f (take i xs) s"
  apply (induction i arbitrary: s)
  apply (auto simp: take_Suc_conv_app_nth)
  done
  
lemma foldr_by_idx: "foldr f xs s = foldr_idx f xs (length xs) s" apply (subst foldr_idx_eq) by auto  


context
  fixes f :: "'a \<Rightarrow> 's \<Rightarrow> 's" and a :: "'a array"
begin  

function array_foldl_idx where
  "array_foldl_idx i s = (if i<array_length a then array_foldl_idx (i+1) (f (array_get a i) s) else s)"  
  by pat_completeness auto
termination
  apply (relation "measure (\<lambda>(i,_). array_length a - i)")
  apply auto
  done

lemmas [simp del] = array_foldl_idx.simps  

end

lemma array_foldl_idx_refine[simp, array_refine]: "array_foldl_idx f a i s = foldl_idx f (array_\<alpha> a) i s"
  apply (induction i s rule: foldl_idx.induct)
  apply (subst array_foldl_idx.simps)
  apply (subst foldl_idx.simps)
  by fastforce

definition "array_fold f a s \<equiv> array_foldl_idx f a 0 s"
lemma array_fold_refine[simp, array_refine]: "array_fold f a s = fold f (array_\<alpha> a) s"  
  unfolding array_fold_def
  by (simp add: fold_by_idx)


fun array_foldr_idx where
  "array_foldr_idx f xs 0 s = s"
| "array_foldr_idx f xs (Suc i) s = array_foldr_idx f xs i (f (array_get xs i) s)"  
  
lemma array_foldr_idx_refine[simp, array_refine]: "array_foldr_idx f xs i s = foldr_idx f (array_\<alpha> xs) i s"
  apply (induction i arbitrary: s)
  by auto  
    
definition "array_foldr f xs s \<equiv> array_foldr_idx f xs (array_length xs) s"  
  
lemma array_foldr_refine[simp, array_refine]: "array_foldr f xs s = foldr f (array_\<alpha> xs) s"
  by (simp add: array_foldr_def foldr_by_idx)  


subsection \<open>Code Generator Setup\<close>

subsubsection \<open>Code-Numeral Preparation\<close>


definition [code del]: "array_new' == array_new o nat_of_integer"
definition [code del]: "array_tabulate' n f \<equiv> array_tabulate (nat_of_integer n) (f o integer_of_nat)"

definition [code del]: "array_length' == integer_of_nat o array_length"
definition [code del]: "array_get' a == array_get a o nat_of_integer"
definition [code del]: "array_set' a == array_set a o nat_of_integer"
definition [code del]:
  "array_get_oo' x a == array_get_oo x a o nat_of_integer"
definition [code del]:
  "array_set_oo' f a == array_set_oo f a o nat_of_integer"


lemma [code]:
  "array_new == array_new' o integer_of_nat"
  "array_tabulate n f == array_tabulate' (integer_of_nat n) (f o nat_of_integer)"
  "array_length == nat_of_integer o array_length'"
  "array_get a == array_get' a o integer_of_nat"
  "array_set a == array_set' a o integer_of_nat"
  "array_get_oo x a == array_get_oo' x a o integer_of_nat"
  "array_set_oo g a == array_set_oo' g a o integer_of_nat"
  by (simp_all
    del: array_refine
    add: o_def
    add: array_new'_def array_tabulate'_def array_length'_def array_get'_def array_set'_def
      array_get_oo'_def array_set_oo'_def)

text \<open>Fallbacks\<close>

lemmas array_get_oo'_fallback[code] = array_get_oo'_def[unfolded array_get_oo_def[abs_def]]
lemmas array_set_oo'_fallback[code] = array_set_oo'_def[unfolded array_set_oo_def[abs_def]]

lemma array_tabulate'_fallback[code]: 
  "array_tabulate' n f = array_of_list (map (f o integer_of_nat) [0..<nat_of_integer n])"
  unfolding array_tabulate'_def 
  by (simp add: array_eq_iff tabulate_def)

lemma array_new'_fallback[code]: "array_new' n x = array_of_list (replicate (nat_of_integer n) x)"  
  by (simp add: array_new'_def array_eq_iff)
  

(*
  Primitive operations, to be implemented for target:
  
    array_of_list
    array_tabulate' (dflt via of_list)
    array_new' (dflt via of_list)

    array_length'
    array_get'
    array_set'
    array_get_oo' (dflt via array_get)

*)
  
  
subsubsection \<open>Haskell\<close>

code_printing type_constructor array \<rightharpoonup>
  (Haskell) "Array.ArrayType/ _"

code_reserved Haskell array_of_list

(*
code_printing code_module "Array" \<rightharpoonup>
  (Haskell) {*
--import qualified Data.Array.Diff as Arr;
import qualified Data.Array as Arr;
import Data.Array.IArray;
import Nat;

instance Ix Nat where {
    range (Nat a, Nat b) = map Nat (range (a, b));
    index (Nat a, Nat b) (Nat c) = index (a,b) c;
    inRange (Nat a, Nat b) (Nat c) = inRange (a, b) c;
    rangeSize (Nat a, Nat b) = rangeSize (a, b);
};

type ArrayType = Arr.DiffArray Nat;
--type ArrayType = Arr.Array Nat;

-- we need to start at 1 and not 0, because the empty array
-- is modelled by having s > e for (s,e) = bounds
-- and as we are in Nat, 0 is the smallest number

array_of_size :: Nat -> [e] -> ArrayType e;
array_of_size n = Arr.listArray (1, n);

array_new :: e -> Nat -> ArrayType e;
array_new a n = array_of_size n (repeat a);

array_length :: ArrayType e -> Nat;
array_length a = let (s, e) = bounds a in if s > e then 0 else e - s + 1;
-- the `if` is actually needed, because in Nat we have s > e --> e - s + 1 = 1

array_get :: ArrayType e -> Nat -> e;
array_get a i = a ! (i + 1);

array_set :: ArrayType e -> Nat -> e -> ArrayType e;
array_set a i e = a // [(i + 1, e)];

array_of_list :: [e] -> ArrayType e;
array_of_list xs = array_of_size (fromInteger (toInteger (length xs - 1))) xs;

array_grow :: ArrayType e -> Nat -> e -> ArrayType e;
array_grow a i x = let (s, e) = bounds a in Arr.listArray (s, e+i) (Arr.elems a ++ repeat x);

array_shrink :: ArrayType e -> Nat -> ArrayType e;
array_shrink a sz = if sz > array_length a then undefined else array_of_size sz (Arr.elems a);
*}
*)

(* TODO/FIXME: Using standard functional arrays here, as DiffArray seems 
  to be discontinued in Haskell! *)
code_printing code_module "Array" \<rightharpoonup>
  (Haskell) \<open>module Array where {

--import qualified Data.Array.Diff as Arr;
import qualified Data.Array as Arr;

type ArrayType = Arr.Array Integer;


array_of_size :: Integer -> [e] -> ArrayType e;
array_of_size n = Arr.listArray (0, n-1);

array_new :: Integer -> e -> ArrayType e;
array_new n a = array_of_size n (repeat a);

array_length :: ArrayType e -> Integer;
array_length a = let (s, e) = Arr.bounds a in e;

array_get :: ArrayType e -> Integer -> e;
array_get a i = a Arr.! i;

array_set :: ArrayType e -> Integer -> e -> ArrayType e;
array_set a i e = a Arr.// [(i, e)];

array_of_list :: [e] -> ArrayType e;
array_of_list xs = array_of_size (toInteger (length xs)) xs;

}\<close>




code_printing constant Array \<rightharpoonup> (Haskell) "Array.array'_of'_list"
code_printing constant array_new' \<rightharpoonup> (Haskell) "Array.array'_new"
code_printing constant array_length' \<rightharpoonup> (Haskell) "Array.array'_length"
code_printing constant array_get' \<rightharpoonup> (Haskell) "Array.array'_get"
code_printing constant array_set' \<rightharpoonup> (Haskell) "Array.array'_set"
code_printing constant array_of_list \<rightharpoonup> (Haskell) "Array.array'_of'_list"

subsubsection \<open>SML\<close>

text \<open>
  We have the choice between single-threaded arrays, that raise an exception if an old version is accessed,
  and truly functional arrays, that update the array in place, but store undo-information to restore
  old versions.
\<close>

code_printing code_module "FArray" \<rightharpoonup>
  (SML)
\<open>
structure FArray = struct
  datatype 'a Cell = Value of 'a Array.array | Upd of (int*'a*'a Cell Unsynchronized.ref);

  type 'a array = 'a Cell Unsynchronized.ref;

  fun array (size,v) = Unsynchronized.ref (Value (Array.array (size,v)));
  fun tabulate (size, f) = Unsynchronized.ref (Value (Array.tabulate(size, f)));
  fun fromList l = Unsynchronized.ref (Value (Array.fromList l));

  fun sub (Unsynchronized.ref (Value a), idx) = Array.sub (a,idx) |
      sub (Unsynchronized.ref (Upd (i,v,cr)),idx) =
        if i=idx then v
        else sub (cr,idx);

  fun length (Unsynchronized.ref (Value a)) = Array.length a |
      length (Unsynchronized.ref (Upd (i,v,cr))) = length cr;

  fun realize_aux (aref, v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let
          val len = Array.length a;
          val a' = Array.array (len,v);
        in
          Array.copy {src=a, dst=a', di=0};
          Unsynchronized.ref (Value a')
        end
      ) |
      (Unsynchronized.ref (Upd (i,v,cr))) => (
        let val res=realize_aux (cr,v) in
          case res of
            (Unsynchronized.ref (Value a)) => (Array.update (a,i,v); res)
        end
      );

  fun realize aref =
    case aref of
      (Unsynchronized.ref (Value _)) => aref |
      (Unsynchronized.ref (Upd (i,v,cr))) => realize_aux(aref,v);

  fun update (aref,idx,v) =
    case aref of
      (Unsynchronized.ref (Value a)) => (
        let val nref=Unsynchronized.ref (Value a) in
          aref := Upd (idx,Array.sub(a,idx),nref);
          Array.update (a,idx,v);
          nref
        end
      ) |
      (Unsynchronized.ref (Upd _)) =>
        let val ra = realize_aux(aref,v) in
          case ra of
            (Unsynchronized.ref (Value a)) => Array.update (a,idx,v);
          ra
        end
      ;


structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun array_new (n:IntInf.int) (a:'a) = array (IntInf.toInt n, a);
fun array_of_list (xs:'a list) = fromList xs;

fun array_tabulate (n:IntInf.int) (f:IntInf.int -> 'a) = tabulate (IntInf.toInt n, f o IntInf.fromInt)

fun array_length (a:'a ArrayType) = IntInf.fromInt (length a);

fun array_get (a:'a ArrayType) (i:IntInf.int) = sub (a, IntInf.toInt i);

fun array_set (a:'a ArrayType) (i:IntInf.int) (e:'a) = update (a, IntInf.toInt i, e);

fun array_get_oo (d:'a) (a:'a ArrayType) (i:IntInf.int) =
  sub (a,IntInf.toInt i) handle Subscript => d

fun array_set_oo (d:(unit->'a ArrayType)) (a:'a ArrayType) (i:IntInf.int) (e:'a) =
  update (a, IntInf.toInt i, e) handle Subscript => d ()

end;
end;


\<close>


code_printing
  type_constructor array \<rightharpoonup> (SML) "_/ FArray.IsabelleMapping.ArrayType"
| constant Array \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_of'_list"
| constant array_new' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_new"
| constant array_tabulate' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_tabulate"
| constant array_length' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_length"
| constant array_get' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_get"
| constant array_set' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_set"
| constant array_of_list \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_of'_list"
| constant array_get_oo' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_get'_oo"
| constant array_set_oo' \<rightharpoonup> (SML) "FArray.IsabelleMapping.array'_set'_oo"


subsubsection \<open>Scala\<close>
text \<open>
  We use a DiffArray-Implementation in Scala.
\<close>
code_printing code_module "DiffArray" \<rightharpoonup>
  (Scala) \<open>
object DiffArray {

  import scala.collection.mutable.ArraySeq

  protected abstract sealed class DiffArray_D[A]
  final case class Current[A] (a:ArraySeq[AnyRef]) extends DiffArray_D[A]
  final case class Upd[A] (i:Int, v:A, n:DiffArray_D[A]) extends DiffArray_D[A]

  object DiffArray_Realizer {
    def realize[A](a:DiffArray_D[A]) : ArraySeq[AnyRef] = a match {
      case Current(a) => ArraySeq.empty ++ a
      case Upd(j,v,n) => {val a = realize(n); a.update(j, v.asInstanceOf[AnyRef]); a}
    }
  }

  class T[A] (var d:DiffArray_D[A]) {

    def realize (): ArraySeq[AnyRef] = { val a=DiffArray_Realizer.realize(d); d = Current(a); a }
    override def toString() = realize().toSeq.toString

    override def equals(obj:Any) =
      if (obj.isInstanceOf[T[A]]) obj.asInstanceOf[T[A]].realize().equals(realize())
      else false

  }


  def array_of_list[A](l : List[A]) : T[A] = new T(Current(ArraySeq.empty ++ l.asInstanceOf[List[AnyRef]]))
  def array_new[A](sz : BigInt, v:A) = new T[A](Current[A](ArraySeq.fill[AnyRef](sz.intValue)(v.asInstanceOf[AnyRef])))

  private def length[A](a:DiffArray_D[A]) : BigInt = a match {
    case Current(a) => a.length
    case Upd(_,_,n) => length(n)
  }

  def length[A](a : T[A]) : BigInt = length(a.d)

  private def sub[A](a:DiffArray_D[A], i:Int) : A = a match {
    case Current(a) => a(i).asInstanceOf[A]
    case Upd(j,v,n) => if (i==j) v else sub(n,i)
  }

  def get[A](a:T[A], i:BigInt) : A = sub(a.d,i.intValue)

  private def realize[A](a:DiffArray_D[A]): ArraySeq[AnyRef] = DiffArray_Realizer.realize[A](a)

  def set[A](a:T[A], i:BigInt,v:A) : T[A] = a.d match {
    case Current(ad) => {
      val ii = i.intValue;
      a.d = Upd(ii,ad(ii).asInstanceOf[A],a.d);
      //ad.update(ii,v);
      ad(ii)=v.asInstanceOf[AnyRef]
      new T[A](Current(ad))
    }
    case Upd(_,_,_) => set(new T[A](Current(realize(a.d))), i.intValue,v)
  }


  def get_oo[A](d: => A, a:T[A], i:BigInt):A = try get(a,i) catch {
    case _:scala.IndexOutOfBoundsException => d
  }

  def set_oo[A](d: Unit => T[A], a:T[A], i:BigInt, v:A) : T[A] = try set(a,i,v) catch {
    case _:scala.IndexOutOfBoundsException => d(())
  }

}

object Test {



  def assert (b : Boolean) : Unit = if (b) () else throw new java.lang.AssertionError("Assertion Failed")

  def eql[A] (a:DiffArray.T[A], b:List[A]) = assert (a.realize.corresponds(b)((x,y) => x.equals(y)))


  def tests1(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Simple update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Another update
    val c = DiffArray.set(b,3,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::9::Nil)

    // Update of old version (forces realize)
    val d = DiffArray.set(b,2,8)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::9::Nil)
      eql(d,1::2::8::4::Nil)

    }

  def tests2(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Simple update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Grow of current version
/*    val c = DiffArray.grow(b,6,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::4::9::9::Nil)

    // Grow of old version
    val d = DiffArray.grow(a,6,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::4::9::9::Nil)
      eql(d,1::2::3::4::9::9::Nil)
*/
  }

  def tests3(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Simple update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
/*
    // Shrink of current version
    val c = DiffArray.shrink(b,3)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::Nil)

    // Shrink of old version
    val d = DiffArray.shrink(a,3)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::9::Nil)
      eql(d,1::2::3::Nil)
*/
  }

  def tests4(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Update _oo (succeeds)
    val b = DiffArray.set_oo((_) => a,a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Update _oo (current version,fails)
    val c = DiffArray.set_oo((_) => a,b,5,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::3::4::Nil)

    // Update _oo (old version,fails)
    val d = DiffArray.set_oo((_) => b,a,5,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)
      eql(c,1::2::3::4::Nil)
      eql(d,1::2::9::4::Nil)

  }

  def tests5(): Unit = {
    val a = DiffArray.array_of_list(1::2::3::4::Nil)
      eql(a,1::2::3::4::Nil)

    // Update
    val b = DiffArray.set(a,2,9)
      eql(a,1::2::3::4::Nil)
      eql(b,1::2::9::4::Nil)

    // Get_oo (current version, succeeds)
      assert (DiffArray.get_oo(0,b,2)==9)
    // Get_oo (current version, fails)
      assert (DiffArray.get_oo(0,b,5)==0)
    // Get_oo (old version, succeeds)
      assert (DiffArray.get_oo(0,a,2)==3)
    // Get_oo (old version, fails)
      assert (DiffArray.get_oo(0,a,5)==0)

  }




  def main(args: Array[String]): Unit = {
    tests1 ()
    tests2 ()
    tests3 ()
    tests4 ()
    tests5 ()


    Console.println("Tests passed")
  }

}

\<close>

code_printing
  type_constructor array \<rightharpoonup> (Scala) "DiffArray.T[_]"
| constant Array \<rightharpoonup> (Scala) "DiffArray.array'_of'_list"
| constant array_new' \<rightharpoonup> (Scala) "DiffArray.array'_new((_).toInt,(_))"
| constant array_length' \<rightharpoonup> (Scala) "DiffArray.length((_)).toInt"
| constant array_get' \<rightharpoonup> (Scala) "DiffArray.get((_),(_).toInt)"
| constant array_set' \<rightharpoonup> (Scala) "DiffArray.set((_),(_).toInt,(_))"
| constant array_of_list \<rightharpoonup> (Scala) "DiffArray.array'_of'_list"
| constant array_get_oo' \<rightharpoonup> (Scala) "DiffArray.get'_oo((_),(_),(_).toInt)"
| constant array_set_oo' \<rightharpoonup> (Scala) "DiffArray.set'_oo((_),(_),(_).toInt,(_))"

context begin
(*private*) definition "test_diffarray_setup \<equiv> (Array,array_new',array_length',array_get', array_set', array_of_list,array_get_oo',array_set_oo')"
export_code test_diffarray_setup checking SML OCaml? Haskell?
end




subsection \<open>Tests\<close> 
(* TODO: Add more systematic tests! *)

definition "test1 \<equiv> 
  let a=array_of_list [1,2,3,4,5,6];
      b=array_tabulate 6 (Suc);
      a'=array_set a 3 42;
      b'=array_set b 3 42;
      c=array_new 6 0
  in
    \<forall>i\<in>{0..<6}. 
      array_get a i = i+1
    \<and> array_get b i = i+1
    \<and> array_get a' i = (if i=3 then 42 else i+1)  
    \<and> array_get b' i = (if i=3 then 42 else i+1)  
    \<and> array_get c i = (0::nat)
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
