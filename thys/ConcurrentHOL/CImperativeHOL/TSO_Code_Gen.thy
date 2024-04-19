(*<*)
theory TSO_Code_Gen
imports
  TSO
begin

(*>*)
subsection \<open> Code generator setup for TSO \label{sec:tso-code_generation} \<close>

text\<open>

The following is only sound if the generated code runs on a machine with a TSO memory model such as:
 \<^item> x86
 \<^item> x86 code running on macOS under Rosetta 2 (ask Google)

Notes:
 \<^item> Haskell: GHC exposes unfenced operations for references and some kinds of arrays
  \<^item> GHC has a zoo of arrays; for now we use the general but inefficient boxed array type
 \<^item> SML: Poly/ML appears to have committed to release/acquire (see email with subject ``Git master update: ARM64, PIE and new bootstrap process'')
  \<^item> on x86 this is TSO
 \<^item> Scala: beyond the scope of this work

TODO:
 \<^item> support a \<^verbatim>\<open>CAS\<close>-like operation
  \<^item> Haskell: \<^url>\<open>https://stackoverflow.com/questions/10102881/haskell-how-does-atomicmodifyioref-work\<close>

\<close>


subsubsection \<open>Haskell\<close>

text\<open>

Adaption layer

\<close>

code_printing code_module "TSOHeap" \<rightharpoonup> (Haskell)
\<open>
module TSOHeap (
    TSO
  , IORef, newIORef, readIORef, writeIORef
  , Array, newArray, newListArray, newFunArray, lengthArray, readArray, writeArray
  , parallel
  ) where

import Control.Concurrent (forkIO)
import qualified Control.Concurrent.MVar as MVar
import qualified Data.Array.IO as Array -- FIXME boxed, contemplate the menagerie of other arrays; perhaps type families might help here
import Data.IORef (IORef, newIORef, readIORef, writeIORef)
import Data.List (genericLength)

type TSO a = IO a
type Array a = Array.IOArray Integer a
type Ref a = Data.IORef.IORef a

writeIORef :: IORef a -> a -> IO ()
writeIORef = writeIORef -- FIXME strict variant?

newArray :: Integer -> a -> IO (Array a)
newArray k = Array.newArray (0, k - 1)

newListArray :: [a] -> IO (Array a)
newListArray xs = Array.newListArray (0, genericLength xs - 1) xs

newFunArray :: Integer -> (Integer -> a) -> IO (Array a)
newFunArray k f = Array.newListArray (0, k - 1) (map f [0..k-1])

lengthArray :: Array a -> IO Integer
lengthArray a = Array.getBounds a >>= return . (\(_, l) -> l + 1)

readArray :: Array a -> Integer -> IO a
readArray = Array.readArray

writeArray :: Array a -> Integer -> a -> IO ()
writeArray = Array.writeArray

-- note we don't want "forkFinally" as we don't model exceptions
parallel :: IO () -> IO () -> IO ()
parallel p q = do
  mvar <- MVar.newEmptyMVar
  forkIO (p >> MVar.putMVar mvar ()) -- FIXME putMVar is lazy
  b <- q
  a <- MVar.takeMVar mvar
  return ()
\<close>

code_reserved Haskell TSOHeap

text \<open>Monad\<close>

code_printing type_constructor tso \<rightharpoonup> (Haskell) "TSOHeap.TSO _"
code_monad tso.bind Haskell
code_printing constant tso.return \<rightharpoonup> (Haskell) "return"
code_printing constant tso.raise \<rightharpoonup> (Haskell) "error"
code_printing constant tso.parallel \<rightharpoonup> (Haskell) "TSOHeap.parallel"

text \<open>Intermediate operation avoids invariance problem in \<open>Scala\<close> (similar to value restriction)\<close>

setup \<open>Sign.mandatory_path "tso.Ref"\<close>

definition ref' where
  [code del]: "ref' = tso.Ref.ref"

lemma [code]:
  "tso.Ref.ref x = tso.Ref.ref' x"
  by (simp add: tso.Ref.ref'_def)

setup \<open>Sign.parent_path\<close>

text \<open>Haskell\<close>

code_printing type_constructor ref \<rightharpoonup> (Haskell) "TSOHeap.Ref _"
code_printing constant Ref \<rightharpoonup> (Haskell) "error/ \"bare Ref\""
code_printing constant tso.Ref.ref' \<rightharpoonup> (Haskell) "TSOHeap.newIORef"
code_printing constant tso.Ref.lookup \<rightharpoonup> (Haskell) "TSOHeap.readIORef"
code_printing constant tso.Ref.update \<rightharpoonup> (Haskell) "TSOHeap.writeIORef"
code_printing constant "HOL.equal :: 'a ref \<Rightarrow> 'a ref \<Rightarrow> bool" \<rightharpoonup> (Haskell) infix 4 "=="
code_printing class_instance ref :: HOL.equal \<rightharpoonup> (Haskell) -

(*<*)

end
(*>*)
