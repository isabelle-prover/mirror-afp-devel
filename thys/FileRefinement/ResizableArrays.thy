header "Resizable arrays"
theory ResizableArrays imports Main begin

text {* These arrays resize themselves, padding with fillValue. *}

types
  'a rArray = "nat * (nat => 'a)"

constdefs
  fillAndUpdate :: "nat => (nat => 'a) => nat => 'a => 'a => (nat => 'a)"
  "fillAndUpdate len f i value fillValue j ==
     if j=i then value
     else if (len <= j & j < i) then fillValue
     else f j"

constdefs
  raWrite :: "'a rArray => nat => 'a => 'a => 'a rArray"
  "raWrite arr i value fillValue ==    
   (let len = fst arr;
        f = snd arr
    in
     if i < len then (len,f(i:=value))
     else (i+1, fillAndUpdate len f i value fillValue)
   )"

constdefs
  cutoff :: "'a => 'a rArray => 'a rArray"
  "cutoff fill arr == 
     (fst arr, 
      % i. if i < fst arr then snd arr i else fill)"

lemma raWriteSizeSame [simp]: "i < fst arr ==> fst (raWrite arr i value fillValue) = fst arr"
by (simp_all add: raWrite_def fillAndUpdate_def Let_def)

lemma raWriteSizeGrows [simp]: "(fst arr <= i) ==> fst (raWrite arr i value fillValue) = i+1"
by (simp_all add: raWrite_def fillAndUpdate_def Let_def)

lemma raWriteContentChanged [simp]: "snd (raWrite arr i value fillValue) i = value"
by (simp_all add: raWrite_def fillAndUpdate_def Let_def)

lemma raWriteContentOld [simp]: "[| j < fst arr; i ~= j |] ==> 
                          snd (raWrite arr i value fillValue) j = snd arr j"
by (simp_all add: raWrite_def fillAndUpdate_def Let_def)

lemma raWriteContentFill [simp]: "[| fst arr < j; j < i |] ==> 
                          snd (raWrite arr i value fillValue) j = fillValue"
by (simp_all add: raWrite_def fillAndUpdate_def Let_def)

end
