(*  
    Title:      IArray_Haskell.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section{*Code Generation from IArrays to Haskell*}

theory IArray_Haskell
  imports IArray_Addenda
begin

subsection{*Code Generation to Haskell*}

text{*The following code is included to import into our namespace 
  the modules and classes to which our serialisation will be mapped*}

(*We map iarrays in Isabelle to Data.Array.IArray.array in Haskell. 
  Performance mapping to Data.Array.Unboxed.Array and Data.Array.Array is similar*)

code_printing code_module "IArray" => (Haskell) {*
  import qualified Data.Array.IArray;
  import qualified Data.Array.Base;
  import qualified Data.Ix;
  import qualified System.IO;
  import qualified Data.List;

  -- The following is largely inspired by the heap monad theory in the Imperative HOL Library

  -- We restrict ourselves to immutable arrays whose indexes are Integer

  type IArray e = Data.Array.IArray.Array Integer e;

  -- The following function constructs an immutable array from an upper bound and a function;
  -- It is the equivalent to SML Vector.of_fun:

  array :: (Integer -> e) -> Integer -> IArray e;
  array f k = Data.Array.IArray.array (0, k - 1) (map (\i -> let fi = f i in fi `seq` (i, f i)) [0..k - 1]) ;
  
  -- The following function is the equivalent to "IArray" type constructor in the SML code
  -- generation setup;
  -- The function length returns a term of type Int, from which we cast to an Integer
  
  listIArray :: [e] -> IArray e;
  listIArray l = Data.Array.IArray.listArray (0, (toInteger . length) l - 1) l;

  -- The access operation for IArray, denoted by ! as an infix operator;
  -- in SML it was denoted as "Vector.sub";
  -- note that SML "Vector.sub" has a single parameter, a pair, 
  -- whereas Haskell "(!)"  has two different parameters; 
  -- that's why we introduce "sub" in Haskell

  infixl 9 !;

  (!) :: IArray e -> Integer -> e;
  v ! i = v `Data.Array.Base.unsafeAt` fromInteger i;

  sub :: (IArray e, Integer) -> e;
  sub (v, i) = v ! i;
  
  -- We use the name lengthIArray to avoid clashes with Prelude.length, usual length for lists:

  lengthIArray :: IArray e -> Integer;
  lengthIArray v = toInteger (Data.Ix.rangeSize (Data.Array.IArray.bounds v));

  -- An equivalent to the Vector.find SML function;
  -- we introduce an auxiliary recursive function
  
  findr :: (e -> Bool) -> Integer -> IArray e -> Maybe e;
  findr f i v = (if ((lengthIArray v - 1) < i) then Nothing
                               else case f (v ! i) of 
                                         True -> Just (v ! i)
                                         False -> findr f (i + 1) v);

  -- The definition of find is as follows

  find :: (e -> Bool) -> IArray e -> Maybe e;
  find f v = findr f 0 v;
  
  -- The definition of the SML function "Vector.exists", based on "find"

  existsIArray :: (e -> Bool) -> IArray e -> Bool;
  existsIArray f v = (case (find f v) of {Nothing -> False;
                                           _      -> True});

  -- The definition of the SML function "Vector.all", based on Haskell in "existsIArray"

  allIArray :: (e -> Bool) -> IArray e -> Bool;
  allIArray f v = not (existsIArray (\x -> not (f x)) v);  
*}

code_reserved Haskell IArray

code_printing type_constructor iarray \<rightharpoonup> (Haskell) "IArray.IArray _"

text{*We use the type @{typ integer} for both indexes and the length of
  @{typ "'a iarray"}; read  the comments
  about the library Code Numeral in the code generation manual, where
  integer and natural are suggested as more appropriate for representing
  indexes of arrays in target-language arrays.*}

code_printing
  constant IArray \<rightharpoonup> (Haskell) "IArray.listIArray"
  | constant IArray.sub' \<rightharpoonup> (Haskell)  "IArray.sub"
  | constant IArray.length' \<rightharpoonup> (Haskell) "IArray.lengthIArray"
  | constant IArray.tabulate \<rightharpoonup> (Haskell) "(let x = _ in (IArray.array (snd x) (fst x)))"

text{*The following functions were generated for our examples in SML, in the file
  @{text IArray_Addenda.thy}, and are also introduced here for Haskell:*}

code_printing
   constant IArray_Addenda.exists \<rightharpoonup> (Haskell) "IArray.existsIArray"
  | constant IArray_Addenda.all \<rightharpoonup> (Haskell) "IArray.allIArray"

code_printing
  class_instance iarray :: "HOL.equal" \<rightharpoonup> (Haskell) -

end
