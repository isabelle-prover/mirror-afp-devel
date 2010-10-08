header {* Arrays with in-place updates *}
theory Array imports 
  AssocList_add
  "Misc"
begin

datatype 'a array = Array "'a list"

subsection {* primitive operations *}

definition new_array :: "'a \<Rightarrow> nat \<Rightarrow> 'a array"
where "new_array a n = Array (replicate n a)"

primrec array_length :: "'a array \<Rightarrow> nat"
where "array_length (Array a) = length a"

primrec array_get :: "'a array \<Rightarrow> nat \<Rightarrow> 'a"
where "array_get (Array a) n = a ! n"

primrec array_set :: "'a array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array"
where "array_set (Array A) n a = Array (A[n := a])"

definition array_of_list :: "'a list \<Rightarrow> 'a array"
where "array_of_list = Array"

  -- "Grows array by @{text inc} elements initialized to value @{text x}."
primrec array_grow :: "'a array \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> 'a array"
  where "array_grow (Array A) inc x = Array (A @ replicate inc x)"

  -- {*Shrinks array to new size @{text sz}. Undefined if @{text "sz > array_length"}*}
primrec array_shrink :: "'a array \<Rightarrow> nat \<Rightarrow> 'a array"
  where "array_shrink (Array A) sz = (
  if (sz > length A) then
    undefined
  else
    Array (take sz A)
  )"

subsection {* Derived operations *}

primrec list_of_array :: "'a array \<Rightarrow> 'a list"
where "list_of_array (Array a) = a"

primrec assoc_list_of_array :: "'a array \<Rightarrow> (nat \<times> 'a) list"
where "assoc_list_of_array (Array a) = zip [0..<length a] a"

function assoc_list_of_array_code :: "'a array \<Rightarrow> nat \<Rightarrow> (nat \<times> 'a) list"
where [simp del]:
  "assoc_list_of_array_code a n =
  (if array_length a \<le> n then []
   else (n, array_get a n) # assoc_list_of_array_code a (n + 1))"
by pat_completeness auto
termination assoc_list_of_array_code
by(relation "measure (\<lambda>p. (array_length (fst p) - snd p))") auto

definition array_map :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a array \<Rightarrow> 'b array"
where "array_map f a = array_of_list (map (\<lambda>(i, v). f i v) (assoc_list_of_array a))"

definition array_foldr :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a array \<Rightarrow> 'b \<Rightarrow> 'b"
where "array_foldr f a b = foldr (\<lambda>(k, v). f k v) (assoc_list_of_array a) b"

definition array_foldl :: "(nat \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'b \<Rightarrow> 'a array \<Rightarrow> 'b"
where "array_foldl f b a = foldl (\<lambda>b (k, v). f k b v) b (assoc_list_of_array a)"

subsection {* Lemmas *}

lemma array_length_new_array [simp]:
  "array_length (new_array a n) = n"
by(simp add: new_array_def)

lemma array_length_array_set [simp]:
  "array_length (array_set a i e) = array_length a"
by(cases a) simp

lemma array_get_new_array [simp]:
  "i < n \<Longrightarrow> array_get (new_array a n) i = a"
by(simp add: new_array_def)

lemma array_get_array_set_same [simp]:
  "n < array_length A \<Longrightarrow> array_get (array_set A n a) n = a"
by(cases A) simp

lemma array_get_array_set_other:
  "n \<noteq> n' \<Longrightarrow> array_get (array_set A n a) n' = array_get A n'"
by(cases A) simp

lemma list_of_array_grow [simp]: 
  "list_of_array (array_grow a inc x) = list_of_array a @ replicate inc x"
by (cases a) (simp)

lemma array_grow_length [simp]:
  "array_length (array_grow a inc x) = array_length a + inc"
by (cases a)(simp add: array_of_list_def)

lemma array_grow_get [simp]: 
  "i < array_length a \<Longrightarrow> array_get (array_grow a inc x) i = array_get a i"
  "\<lbrakk> i \<ge> array_length a;  i < array_length a + inc\<rbrakk> \<Longrightarrow> array_get (array_grow a inc x) i = x"
by (cases a, simp add: nth_append)+

lemma list_of_array_shrink [simp]:
  "\<lbrakk> s \<le> array_length a\<rbrakk> \<Longrightarrow> list_of_array (array_shrink a s) = take s (list_of_array a)"
by (cases a) simp

lemma array_shrink_get [simp]:
  "\<lbrakk> i < s; s \<le> array_length a \<rbrakk> \<Longrightarrow> array_get (array_shrink a s) i = array_get a i"
by (cases a) (simp)

lemma list_of_array_id [simp]: "list_of_array (array_of_list l) = l"
by (cases l)(simp_all add: array_of_list_def)

lemma map_of_assoc_list_of_array:
  "map_of (assoc_list_of_array a) k = (if k < array_length a then Some (array_get a k) else None)"
by(cases a, cases "k < array_length a")(force simp add: set_zip)+

lemma length_assoc_list_of_array [simp]:
  "length (assoc_list_of_array a) = array_length a"
by(cases a) simp

lemma distinct_assoc_list_of_array:
  "distinct (map fst (assoc_list_of_array a))"
by(cases a)(auto)

lemma array_length_array_map [simp]: 
  "array_length (array_map f a) = array_length a"
by(simp add: array_map_def array_of_list_def)

lemma array_get_array_map [simp]:
  "i < array_length a \<Longrightarrow> array_get (array_map f a) i = f i (array_get a i)"
by(cases a)(simp add: array_map_def map_ran_conv_map array_of_list_def)

lemma array_foldr_foldr:
  "array_foldr (\<lambda>n. f) (Array a) b = foldr f a b"
by(simp add: array_foldr_def foldr_snd_zip)

lemma assoc_list_of_array_code_induct:
  assumes IH: "\<And>n. (n < array_length a \<Longrightarrow> P (Suc n)) \<Longrightarrow> P n"
  shows "P n"
proof -
  have "a = a \<longrightarrow> P n"
    by(rule assoc_list_of_array_code.induct[where P="\<lambda>a' n. a = a' \<longrightarrow> P n"])(auto intro: IH)
  thus ?thesis by simp
qed

lemma assoc_list_of_array_code [code]:
  "assoc_list_of_array a = assoc_list_of_array_code a 0"
proof(cases a)
  case (Array A)
  { fix n
    have "zip [n..<length A] (drop n A) = assoc_list_of_array_code (Array A) n"
    proof(induct n taking: "Array A" rule: assoc_list_of_array_code_induct)
      case (1 n)
      show ?case
      proof(cases "n < array_length (Array A)")
	case False
	thus ?thesis by(simp add: assoc_list_of_array_code.simps)
      next
	case True
	hence "zip [Suc n..<length A] (drop (Suc n) A) = assoc_list_of_array_code (Array A) (Suc n)" by(rule 1)
	moreover from True have "n < length A" by simp
	moreover then obtain a A' where A: "drop n A = a # A'" by(cases "drop n A") auto
	moreover with `n < length A` have [simp]: "a = A ! n"
	  by(subst append_take_drop_id[symmetric, where n=n])(simp add: nth_append min_def)
	moreover from A have "drop (Suc n) A = A'"
	  by(induct A arbitrary: n)(simp_all add: drop_Cons split: nat.split_asm)
	ultimately show ?thesis by(subst upt_rec)(simp add: assoc_list_of_array_code.simps)
      qed
    qed }
  note this[of 0]
  with Array show ?thesis by simp
qed

lemma list_of_array_code [code]:
  "list_of_array a = array_foldr (\<lambda>n. Cons) a []"
by(cases a)(simp add: array_foldr_foldr foldr_Cons)

lemma array_foldr_cong [fundef_cong]:
  "\<lbrakk> a = a'; b = b'; 
    \<And>i b. i < array_length a \<Longrightarrow> f i (array_get a i) b = g i (array_get a i) b \<rbrakk>
  \<Longrightarrow> array_foldr f a b = array_foldr g a' b'"
by(cases a)(auto simp add: array_foldr_def set_zip intro!: foldr_cong)

lemma array_foldl_foldl:
  "array_foldl (\<lambda>n. f) b (Array a) = foldl f b a"
by(simp add: array_foldl_def foldl_snd_zip)

lemma array_map_conv_foldl_array_set:
  assumes len: "array_length A = array_length a"
  shows "array_map f a = foldl (\<lambda>A (k, v). array_set A k (f k v)) A (assoc_list_of_array a)"
proof(cases a)
  case (Array xs)
  obtain ys where [simp]: "A = Array ys" by(cases A)
  with Array len have "length xs \<le> length ys" by simp
  hence "foldr (\<lambda>x y. array_set y (fst x) (f (fst x) (snd x)))
               (rev (zip [0..<length xs] xs)) (Array ys) =
         Array (map (\<lambda>x. f (fst x) (snd x)) (zip [0..<length xs] xs) @ drop (length xs) ys)"
  proof(induct xs arbitrary: ys rule: rev_induct)
    case Nil thus ?case by simp
  next
    case (snoc x xs ys)
    from `length (xs @ [x]) \<le> length ys` have "length xs \<le> length ys" by simp
    hence "foldr (\<lambda>x y. array_set y (fst x) (f (fst x) (snd x)))
                 (rev (zip [0..<length xs] xs)) (Array ys) =
           Array (map (\<lambda>x. f (fst x) (snd x)) (zip [0..<length xs] xs) @ drop (length xs) ys)"
      by(rule snoc)
    moreover from `length (xs @ [x]) \<le> length ys`
    obtain y ys' where ys: "drop (length xs) ys = y # ys'"
      by(cases "drop (length xs) ys") auto
    moreover hence "drop (Suc (length xs)) ys = ys'" by(auto dest: drop_eq_ConsD)
    ultimately show ?case by(simp add: list_update_append)
  qed
  thus ?thesis using Array len
    by(simp add: array_map_def split_beta array_of_list_def foldl_foldr)
qed

subsection {* Lemmas about empty arrays *}

lemma array_length_eq_0 [simp]:
  "array_length a = 0 \<longleftrightarrow> a = Array []"
by(cases a) simp

lemma new_array_0 [simp]: "new_array v 0 = Array []"
by(simp add: new_array_def)

lemma array_of_list_Nil [simp]:
  "array_of_list [] = Array []"
by(simp add: array_of_list_def)

lemma array_map_Nil [simp]:
  "array_map f (Array []) = Array []"
by(simp add: array_map_def)

lemma array_foldl_Nil [simp]:
  "array_foldl f b (Array []) = b"
by(simp add: array_foldl_def)

lemma array_foldr_Nil [simp]:
  "array_foldr f (Array []) b = b"
by(simp add: array_foldr_def)

lemma prod_foldl_conv:
  "(foldl f a xs, foldl g b xs) = foldl (\<lambda>(a, b) x. (f a x, g b x)) (a, b) xs"
by(induct xs arbitrary: a b) simp_all

lemma prod_array_foldl_conv:
  "(array_foldl f b a, array_foldl g c a) = array_foldl (\<lambda>h (b, c) v. (f h b v, g h c v)) (b, c) a" 
by(cases a)(simp add: array_foldl_def foldl_map prod_foldl_conv split_def)

lemma array_foldl_array_foldr_comm:
  "fun_left_comm (\<lambda>(h, v) b. f h b v) \<Longrightarrow> array_foldl f b a = array_foldr (\<lambda>h v b. f h b v) a b"
by(cases a)(simp add: array_foldl_def array_foldr_def split_def fun_left_comm.foldr_conv_foldl)

lemma array_map_conv_array_foldl:
  "array_map f a = array_foldl (\<lambda>h a v. array_set a h (f h v)) a a"
proof(cases a)
  case (Array xs)
  def a == xs
  hence "length xs \<le> length a" by simp
  hence "foldl (\<lambda>a (k, v). array_set a k (f k v))
              (Array a) (zip [0..<length xs] xs)
         = Array (map (\<lambda>(k, v). f k v) (zip [0..<length xs] xs) @ drop (length xs) a)"
  proof(induct xs rule: rev_induct)
    case Nil thus ?case by simp
  next
    case (snoc x xs)
    have "foldl (\<lambda>a (k, v). array_set a k (f k v)) (Array a) (zip [0..<length (xs @ [x])] (xs @ [x])) = 
          array_set (foldl (\<lambda>a (k, v). array_set a k (f k v)) (Array a) (zip [0..<length xs] xs))
                    (length xs) (f (length xs) x)" by simp
    also from `length (xs @ [x]) \<le> length a` have "length xs \<le> length a" by simp
    hence "foldl (\<lambda>a (k, v). array_set a k (f k v)) (Array a) (zip [0..<length xs] xs) =
           Array (map (\<lambda>(k, v). f k v) (zip [0..<length xs] xs) @ drop (length xs) a)" by(rule snoc)
    also note array_set.simps
    also have "(map (\<lambda>(k, v). f k v) (zip [0..<length xs] xs) @ drop (length xs) a) [length xs := f (length xs) x] =
              map (\<lambda>(k, v). f k v) (zip [0..<length xs] xs) @ (drop (length xs) a[0 := f (length xs) x])"
      by(simp add: list_update_append)
    also from `length (xs @ [x]) \<le> length a`
    have "drop (length xs) a[0 := f (length xs) x] =
          f (length xs) x # drop (Suc (length xs)) a"
      by(simp add: upd_conv_take_nth_drop)
    also have "map (\<lambda>(k, v). f k v) (zip [0..<length xs] xs) @ f (length xs) x # drop (Suc (length xs)) a =
             (map (\<lambda>(k, v). f k v) (zip [0..<length xs] xs) @ [f (length xs) x]) @ drop (Suc (length xs)) a" by simp
    also have "\<dots> = map (\<lambda>(k, v). f k v) (zip [0..<length (xs @ [x])] (xs @ [x])) @ drop (length (xs @ [x])) a"
      by(simp)
    finally show ?case .
  qed
  with a_def Array show ?thesis
    by(simp add: array_foldl_def array_map_def array_of_list_def)
qed

lemma array_foldl_new_array:
  "array_foldl f b (new_array a n) = foldl (\<lambda>b (k, v). f k b v) b (zip [0..<n] (replicate n a))"
by(simp add: new_array_def array_foldl_def)


subsection {* Code Generator Setup *}

subsubsection {* Code generator setup for Haskell *}

code_type array 
  (Haskell "Array.ArrayType/ _")

code_reserved Haskell array_of_list

(* TODO: No code for grow and shrink yet *)

code_include Haskell "Array"
{*
import qualified Data.Array.Diff;
import Data.Array.IArray;

type ArrayType = Data.Array.Diff.DiffArray Int;

new_array :: e -> Int -> ArrayType e;
new_array a n = Data.Array.Diff.listArray (0, n - 1) (take n (repeat a));

array_length :: ArrayType e -> Int;
array_length a = let (s, e) = bounds a in e - s + 1;

array_get :: ArrayType e -> Int -> e;
array_get a i = a ! i;

array_set :: ArrayType e -> Int -> e -> ArrayType e;
array_set a i e = a // [(i, e)];

array_of_list :: [e] -> ArrayType e;
array_of_list xs = Data.Array.Diff.listArray (0, length xs - 1) xs;

*}

code_const Array (Haskell "Array.array'_of'_list")
code_const new_array (Haskell "Array.new'_array")
code_const array_length (Haskell "Array.array'_length")
code_const array_get (Haskell "Array.array'_get")
code_const array_set (Haskell "Array.array'_set")
code_const array_of_list (Haskell "Array.array'_of'_list")


subsubsection {* Code Generator Setup For SML *}

text {* 
  We have the choice between single-threaded arrays, that raise an exception if an old version is accessed,
  and truly functional arrays, that update the array in place, but store undo-information to restore
  old versions.
 *}

code_include SML "STArray"
{*
structure STArray = struct

datatype 'a Cell = Invalid | Value of 'a array;

exception AccessedOldVersion;

type 'a array = 'a Cell Unsynchronized.ref;

fun fromList l = Unsynchronized.ref (Value (Array.fromList l));
fun array (size, v) = Unsynchronized.ref (Value (Array.array (size,v)));
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

fun grow (aref, i, x) = case aref of 
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    let val len=Array.length a;
        val na = Array.array (len+i,x) 
    in
      aref := Invalid;
      Array.copy {src=a, dst=na, di=0};
      Unsynchronized.ref (Value na)
    end
    );

fun shrink (aref, sz) = case aref of
  (Unsynchronized.ref Invalid) => raise AccessedOldVersion |
  (Unsynchronized.ref (Value a)) => (
    if sz > Array.length a then 
      raise Size
    else (
      aref:=Invalid;
      Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
    )
  );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:int) = array (n, a);

fun array_length (a:'a ArrayType) = length a;

fun array_get (a:'a ArrayType) (i:int) = sub (a, i);

fun array_set (a:'a ArrayType) (i:int) (e:'a) = update (a, i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:int) (x:'a) = grow (a, i, x);

fun array_shrink (a:'a ArrayType) (sz:int) = shrink (a,sz);

end;

end;

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

  fun grow (aref, inc, x) = case aref of 
    (Unsynchronized.ref (Value a)) => (
      let val len=Array.length a;
          val na = Array.array (len+inc,x) 
      in
        Array.copy {src=a, dst=na, di=0};
        Unsynchronized.ref (Value na)
      end
      )
  | (Unsynchronized.ref (Upd _)) => (
    grow (realize aref, inc, x)
  );

  fun shrink (aref, sz) = case aref of
    (Unsynchronized.ref (Value a)) => (
      if sz > Array.length a then 
        raise Size
      else (
        Unsynchronized.ref (Value (Array.tabulate (sz,fn i => Array.sub (a,i))))
      )
    ) |
    (Unsynchronized.ref (Upd _)) => (
      shrink (realize aref,sz)
    );

structure IsabelleMapping = struct
type 'a ArrayType = 'a array;

fun new_array (a:'a) (n:int) = array (n, a);

fun array_length (a:'a ArrayType) = length a;

fun array_get (a:'a ArrayType) (i:int) = sub (a, i);

fun array_set (a:'a ArrayType) (i:int) (e:'a) = update (a, i, e);

fun array_of_list (xs:'a list) = fromList xs;

fun array_grow (a:'a ArrayType) (i:int) (x:'a) = grow (a, i, x);

fun array_shrink (a:'a ArrayType) (sz:int) = shrink (a,sz);

end;
end;


*}

code_type array 
  (SML "_/ FArray.IsabelleMapping.ArrayType")

code_const Array (SML "FArray.IsabelleMapping.array'_of'_list")
code_const new_array (SML "FArray.IsabelleMapping.new'_array")
code_const array_length (SML "FArray.IsabelleMapping.array'_length")
code_const array_get (SML "FArray.IsabelleMapping.array'_get")
code_const array_set (SML "FArray.IsabelleMapping.array'_set")
code_const array_grow (SML "FArray.IsabelleMapping.array'_grow")
code_const array_shrink (SML "FArray.IsabelleMapping.array'_shrink")
code_const array_of_list (SML "FArray.IsabelleMapping.array'_of'_list")

end
