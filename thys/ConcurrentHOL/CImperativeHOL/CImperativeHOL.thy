(*<*)
theory CImperativeHOL
imports
  Heap
begin

(*>*)
section \<open> A concurrent variant of Imperative HOL\label{sec:CImperativeHOL} \<close>

text\<open>

We model programs operating on sequentially-consistent memory with the  type \<^typ>\<open>(heap.t, 'v) prog\<close>.

Source materials:
 \<^item> \<^file>\<open>$ISABELLE_HOME/src/HOL/Imperative_HOL/Heap_Monad.thy\<close>
 \<^item> \<^file>\<open>$ISABELLE_HOME/src/HOL/Imperative_HOL/Array.thy\<close>
 \<^item> \<^file>\<open>$ISABELLE_HOME/src/HOL/Imperative_HOL/Ref.thy\<close>
  \<^item> note that ImperativeHOL is deterministic and sequential

\<close>

type_synonym 'v imp = "(heap.t, 'v) prog"

setup \<open>Sign.mandatory_path "prog"\<close>

definition raise :: "String.literal \<Rightarrow> 'a imp" where \<comment> \<open>the literal is just decoration\<close>
  "raise s = \<bottom>"

definition assert :: "bool \<Rightarrow> unit imp" where
  "assert P = (if P then prog.return () else prog.raise STR ''assert'')"

setup \<open>Sign.mandatory_path "Ref"\<close>

definition ref :: "'a::heap.rep \<Rightarrow> 'a ref imp" where
  "ref v = prog.action {(r, s, s'). (r, s') \<in> Ref.alloc v s}"

definition lookup :: "'a::heap.rep ref \<Rightarrow> 'a imp" (\<open>!_\<close> 61) where
  "lookup r = prog.read (Ref.get r)"

definition update :: "'a ref \<Rightarrow> 'a::heap.rep \<Rightarrow> unit imp" (\<open>_ := _\<close> 62) where
  "update r v = prog.write (Ref.set r v)"

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "Array"\<close>

definition new :: "('i \<times> 'i) \<Rightarrow> 'a \<Rightarrow> ('i::Ix, 'a::heap.rep) array imp" where
  "new b v = prog.action {(Array b a, s, s') |a s s'. (a, s') \<in> ODArray.alloc (replicate (length (Ix.interval b)) v) s}"

definition make :: "('i \<times> 'i) \<Rightarrow> ('i \<Rightarrow> 'a) \<Rightarrow> ('i::Ix, 'a::heap.rep) array imp" where
  "make b f = prog.action {(Array b a, s, s') |a s s'. (a, s') \<in> ODArray.alloc (map f (Ix.interval b)) s}"

\<comment>\<open> Approximately Haskell's \<^emph>\<open>listArray\<close>: ``Construct an array from a pair of bounds and a list of values in index order.'' \<close>
definition of_list :: "('i \<times> 'i) \<Rightarrow> 'a list \<Rightarrow> ('i::Ix, 'a::heap.rep) array imp" where
  "of_list b xs = prog.action {(Array b a, s, s') |a s s'. length (Ix.interval b) \<le> length xs \<and> (a, s') \<in> ODArray.alloc xs s}"

definition nth :: "('i::Ix, 'a::heap.rep) array \<Rightarrow> 'i \<Rightarrow> 'a imp" where
  "nth a i = prog.read (\<lambda>s. Array.get a i s)"

definition upd :: "('i::Ix, 'a::heap.rep) array \<Rightarrow> 'i \<Rightarrow> 'a \<Rightarrow> unit imp" where
  "upd a i v = prog.write (Array.set a i v)"

\<comment>\<open> derived operations; observe the lack of atomicity \<close>

definition freeze :: "('i::Ix, 'a::heap.rep) array \<Rightarrow> 'a list imp" where
  "freeze a = prog.fold_mapM (prog.Array.nth a) (Array.interval a)"

definition swap :: "('i::Ix, 'a::heap.rep) array \<Rightarrow> 'i \<Rightarrow> 'i \<Rightarrow> unit imp"
where
  "swap a i j =
     do {
       x \<leftarrow> prog.Array.nth a i;
       y \<leftarrow> prog.Array.nth a j;
       prog.Array.upd a i y;
       prog.Array.upd a j x;
       prog.return ()
     }"

declare prog.raise_def[code del]
declare prog.Ref.ref_def[code del]
declare prog.Ref.lookup_def[code del]
declare prog.Ref.update_def[code del]
declare prog.Array.new_def[code del]
declare prog.Array.make_def[code del]
declare prog.Array.of_list_def[code del]
declare prog.Array.nth_def[code del]
declare prog.Array.upd_def[code del]
declare prog.Array.freeze_def[code del]


paragraph\<open> Operations on two-dimensional arrays \<close>

definition fst_app_chaotic :: "('a::Ix, 'b::Ix) two_dim \<Rightarrow> ('a \<Rightarrow> ('s, unit) prog) \<Rightarrow> ('s, unit) prog" where
  "fst_app_chaotic b f = prog.set_app f (set (Ix.interval (fst_bounds b)))"

definition fst_app :: "('a::Ix, 'b::Ix) two_dim \<Rightarrow> ('a \<Rightarrow> ('s, unit) prog) \<Rightarrow> ('s, unit) prog" where
  "fst_app b f = prog.app f (Ix.interval (fst_bounds b))"

lemma fst_app_fst_app_chaotic_le:
  shows "prog.Array.fst_app b f \<le> prog.Array.fst_app_chaotic b f"
unfolding prog.Array.fst_app_chaotic_def prog.Array.fst_app_def
by (strengthen ord_to_strengthen(1)[OF prog.app.set_app_le]) (auto simp: distinct_interval)

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.parent_path\<close>

setup \<open>Sign.mandatory_path "ag.prog"\<close>

lemmas fst_app_chaotic =
  ag.prog.app_set[where X="set (Ix.interval (fst_bounds b))" for b, folded prog.Array.fst_app_chaotic_def]
lemmas fst_app =
  ag.prog.app[where xs="Ix.interval (fst_bounds b)" for b, folded prog.Array.fst_app_def]

setup \<open>Sign.parent_path\<close>


subsection \<open>Code generator setup\<close>

subsubsection \<open>Haskell\<close>

code_printing code_module "Heap" \<rightharpoonup> (Haskell)
\<open>
-- Sequentially-consistent primitives
-- Arrays:
--   https://hackage.haskell.org/package/array-0.5.4.0/docs/Data-Array-IO.html
--   https://hackage.haskell.org/package/array-0.5.4.0/docs/src/Data.Array.Base.html
module Heap (
    Prog
  , Ref, newIORef, readIORef, writeIORef
  , Array, newArray, newListArray, newFunArray, readArray, writeArray
  , parallel
  ) where

import Control.Concurrent (forkIO)
import qualified Control.Concurrent.MVar as MVar
import qualified Data.Array.IO as Array
import Data.IORef (IORef, newIORef, readIORef, atomicWriteIORef)
import Data.List (genericLength)

type Prog a b = IO b
type Array a = Array.IOArray Integer a
type Ref a = Data.IORef.IORef a

writeIORef :: IORef a -> a -> IO ()
writeIORef = atomicWriteIORef -- could use the strict variant

newArray :: Integer -> a -> IO (Array a)
newArray k = Array.newArray (0, k - 1)

newFunArray :: Integer -> (Integer -> a) -> IO (Array a)
newFunArray k f = Array.newListArray (0, k - 1) (map f [0..k-1])

newListArray :: Integer -> [a] -> IO (Array a)
newListArray k xs = Array.newListArray (0, k) xs

readArray :: Array a -> Integer -> IO a
readArray = Array.readArray

writeArray :: Array a -> Integer -> a -> IO ()
writeArray = Array.writeArray -- probably should be the WMM atomic op

{-
-- `forkIO` is reputedly cheap, but other papers imply the use of worker threads, perhaps for other reasons
-- note we don't want "forkFinally" as we don't model exceptions
parallel' :: IO a -> IO b -> IO (a, b)
parallel' p q = do
  mvar <- MVar.newEmptyMVar
  forkIO (p >>= MVar.putMVar mvar) -- note putMVar is lazy
  b <- q
  a <- MVar.takeMVar mvar
  return (a, b)
-}

parallel :: IO () -> IO () -> IO ()
parallel p q = do
  mvar <- MVar.newEmptyMVar
  forkIO (p >> MVar.putMVar mvar ()) -- note putMVar is lazy
  b <- q
  a <- MVar.takeMVar mvar
  return ()
\<close>

code_reserved Haskell Ix

code_printing type_constructor prog \<rightharpoonup> (Haskell) "Heap.Prog _ _"
code_monad prog.bind Haskell
code_printing constant prog.return \<rightharpoonup> (Haskell) "return"
code_printing constant prog.raise \<rightharpoonup> (Haskell) "error"
code_printing constant prog.parallel \<rightharpoonup> (Haskell) "Heap.parallel"
(* TODO
code_printing constant prog.Parallel \<rightharpoonup> (Haskell) "Heap.parallel"
*)

text\<open> Intermediate operation avoids invariance problem in \<open>Scala\<close> (similar to value restriction) \<close>

setup \<open>Sign.mandatory_path "Ref"\<close>

definition ref' where
  [code del]: "ref' = prog.Ref.ref"

lemma [code]:
  "prog.Ref.ref x = Ref.ref' x"
by (simp add: Ref.ref'_def)

setup \<open>Sign.parent_path\<close>

code_printing type_constructor ref \<rightharpoonup> (Haskell) "Heap.Ref _"
code_printing constant Ref \<rightharpoonup> (Haskell) "error/ \"bare Ref\""
code_printing constant Ref.ref' \<rightharpoonup> (Haskell) "Heap.newIORef"
code_printing constant prog.Ref.lookup \<rightharpoonup> (Haskell) "Heap.readIORef"
code_printing constant prog.Ref.update \<rightharpoonup> (Haskell) "Heap.writeIORef"
code_printing constant "HOL.equal :: 'a ref \<Rightarrow> 'a ref \<Rightarrow> bool" \<rightharpoonup> (Haskell) infix 4 "=="
code_printing class_instance ref :: HOL.equal \<rightharpoonup> (Haskell) -

text\<open> The target language only has to provide one-dimensional arrays indexed by \<^typ>\<open>integer\<close>. \<close>

setup \<open>Sign.mandatory_path "prog.Array"\<close>

definition new' :: "integer \<Rightarrow> 'a \<Rightarrow> 'a::heap.rep one_dim_array imp" where
  "new' k v = prog.action {(a, s, s') |a s s'. (a, s') \<in> ODArray.alloc (replicate (nat_of_integer k) v) s}"

declare prog.Array.new'_def[code del]

lemma new_new'[code]:
  shows "prog.Array.new b v = prog.Array.new' (of_nat (length (Ix.interval b))) v \<bind> prog.return \<circ> Array b"
by (force simp: prog.Array.new_def prog.Array.new'_def prog.vmap.action
     simp flip: prog.vmap.eq_return
         intro: arg_cong[where f=prog.action])

definition make' :: "integer \<Rightarrow> (integer \<Rightarrow> 'a) \<Rightarrow> 'a::heap.rep one_dim_array imp" where
  "make' k f = prog.action {(a, s, s') |a s s'. (a, s') \<in> ODArray.alloc (map (f \<circ> of_nat) [0..<nat_of_integer k]) s}"

declare prog.Array.make'_def[code del]

lemma make_make'[code]:
  shows "prog.Array.make b f
       = prog.Array.make' (of_nat (length (Ix.interval b))) (\<lambda>i. f (Ix.interval b ! nat_of_integer i))
           \<bind> prog.return \<circ> Array b"
by (force simp: interval_map prog.Array.make_def prog.Array.make'_def prog.vmap.action comp_def
     simp flip: prog.vmap.eq_return
         intro: arg_cong[where f=prog.action])

definition of_list' :: "integer \<Rightarrow> 'a list \<Rightarrow> 'a::heap.rep one_dim_array imp" where
  "of_list' k xs = prog.action {(a, s, s') |a s s'. nat_of_integer k \<le> length xs \<and> (a, s') \<in> ODArray.alloc xs s}"

declare prog.Array.of_list'_def[code del]

lemma of_list_of_list'[code]:
  shows "prog.Array.of_list b xs
       = prog.Array.of_list' (of_nat (length (Ix.interval b))) xs \<bind> prog.return \<circ> Array b"
by (force simp: prog.Array.of_list_def prog.Array.of_list'_def prog.vmap.action
     simp flip: prog.vmap.eq_return
         intro: arg_cong[where f=prog.action])

definition nth' :: "'a::heap.rep one_dim_array \<Rightarrow> integer \<Rightarrow> 'a imp" where
  "nth' a i = prog.read (ODArray.get a (nat_of_integer i))"

declare prog.Array.nth'_def[code del]

lemma nth_nth'[code]:
  shows "prog.Array.nth a i = prog.Array.nth' (array.arr a) (of_nat (Array.index a i))"
by (simp add: prog.Array.nth_def prog.Array.nth'_def Array.get_def)

definition upd' :: "'a::heap.rep one_dim_array \<Rightarrow> integer \<Rightarrow> 'a::heap.rep \<Rightarrow> unit imp" where
  "upd' a i v = prog.write (ODArray.set a (nat_of_integer i) v)"

declare prog.Array.upd'_def[code del]

lemma upd_upd'[code]:
  shows "prog.Array.upd a i v = prog.Array.upd' (array.arr a) (of_nat (Array.index a i)) v"
by (simp add: prog.Array.upd_def prog.Array.upd'_def Array.set_def)

setup \<open>Sign.parent_path\<close>

code_printing type_constructor one_dim_array \<rightharpoonup> (Haskell) "Heap.Array/ _"
code_printing constant one_dim_array.Array \<rightharpoonup> (Haskell) "error/ \"bare Array\""
code_printing constant prog.Array.new' \<rightharpoonup> (Haskell) "Heap.newArray"
code_printing constant prog.Array.make' \<rightharpoonup> (Haskell) "Heap.newFunArray"
code_printing constant prog.Array.of_list' \<rightharpoonup> (Haskell) "Heap.newListArray"
code_printing constant prog.Array.nth' \<rightharpoonup> (Haskell) "Heap.readArray"
code_printing constant prog.Array.upd' \<rightharpoonup> (Haskell) "Heap.writeArray"
code_printing constant "HOL.equal :: ('i, 'a) array \<Rightarrow> ('i, 'a) array \<Rightarrow> bool" \<rightharpoonup> (Haskell) infix 4 "=="
code_printing class_instance array :: HOL.equal \<rightharpoonup> (Haskell) -


subsection\<open> Value-returning parallel\label{sec:CImperativeHOL-parallel} \<close>

definition parallelP' :: "'a::heap.rep imp \<Rightarrow> 'b::heap.rep imp \<Rightarrow> ('a \<times> 'b) imp" where
  "parallelP' P\<^sub>1 P\<^sub>2 = do {
     r\<^sub>1 \<leftarrow> prog.Ref.ref undefined
   ; r\<^sub>2 \<leftarrow> prog.Ref.ref undefined
   ; ((P\<^sub>1 \<bind> prog.Ref.update r\<^sub>1) \<parallel> (P\<^sub>2 \<bind> prog.Ref.update r\<^sub>2))
   ; v\<^sub>1 \<leftarrow> prog.Ref.lookup r\<^sub>1
   ; v\<^sub>2 \<leftarrow> prog.Ref.lookup r\<^sub>2
   ; prog.return (v\<^sub>1, v\<^sub>2)
   }"
(*<*)

end
(*>*)
