header "Arrays without bounds"
theory CArrays imports Main begin

text {* For these arrays there is no
        built-in protection against reading or writing out-of-bounds. *}

types
  'a cArray = "nat => 'a"

constdefs
  makeCArray :: "nat => 'a => 'a cArray"
  "makeCArray arraySize fillValue index == 
   if index < arraySize then fillValue else arbitrary"

constdefs
  readCArray :: "'a cArray => nat => 'a"
  "readCArray array index == array index"

constdefs
  writeCArray :: "'a cArray => nat => 'a => 'a cArray"
  "writeCArray array index value == array(index := value)"

(* ---------------------------------------------------------------*)

lemma makeCArrayCorrect:
  "index < arraySize ==>
   readCArray (makeCArray arraySize fillValue) index = fillValue"
by (simp add: readCArray_def makeCArray_def)

lemma writeCArrayCorrect1:
  "readCArray (writeCArray array index value) index = value"
by (simp add: readCArray_def writeCArray_def)

lemma writeCArrayCorrect2:
  "index1 ~= index2 ==>
   readCArray (writeCArray array index1 value) index2 = 
   readCArray array index2"
by (simp add: readCArray_def writeCArray_def)

end