header{* Register Operations*}
theory RegistersOps
imports Main "../lib/WordDecl" 
begin

text{*
 This theory provides operations to get, set and clear bits in registers
*}

section "Getting Fields"
  
text{* 
  Get a field of type @{typ "'b::len word"} 
  starting at @{term "index"} from @{term "addr"} of type @{typ "'a::len word"}
*}
definition get_field_from_word_a_b:: "'a::len word \<Rightarrow> nat \<Rightarrow> 'b::len word"
 where
  "get_field_from_word_a_b addr index 
    \<equiv> let off = (size addr - len_of TYPE('b)) 
       in ucast ((addr << (off-index)) >> off)"

text{* 
  Obtain, from addr of type @{typ "'a::len word"}, 
  another @{typ "'a::len word"} containing the field of length @{text "len"}
  starting at @{text "index"} in @{text "addr"}. 
*}
definition get_field_from_word_a_a:: "'a::len word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a::len word"
 where
  "get_field_from_word_a_a addr index len 
    \<equiv> (addr << (size addr - (index+len)) >> (size addr - len))"

section "Setting Fields"

text{* 
  Set the field of type @{typ "'b::len word"} 
  at @{text "index"} from @{text "record"}
  of type @{typ "'a::len word"}. 
*}
definition set_field :: "'a::len word \<Rightarrow> 'b::len word \<Rightarrow> nat \<Rightarrow> 'a::len word"
 where 
  "set_field record field index 
    \<equiv> let mask:: ('a::len word) = (mask (size field)) << index 
      in  (record AND (NOT mask)) OR ((ucast field) << index)"


section "Clearing Fields"

text{* 
  Zero the @{text "n"} initial bits of @{text "addr"}.
*}
definition clear_n_bits:: "'a::len word \<Rightarrow> nat \<Rightarrow> 'a::len word" 
 where
   "clear_n_bits addr n \<equiv> addr AND (NOT (mask n))"

text{*
  Gets the natural value of a 32 bit mask 
*}

definition get_nat_from_mask::"word32 \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> (word32 \<times> nat)" 
where
"
get_nat_from_mask w m v \<equiv> if (w AND (mask m) =0) then (w>>m, v+m)
                          else (w,m)
"

definition get_nat_from_mask32::"word32\<Rightarrow> nat"
where
"get_nat_from_mask32 w \<equiv> 
                            if (w=0) then len_of TYPE (word_length32)
                            else
                                let (w,res) = get_nat_from_mask w 16 0 in
                                     let (w,res)= get_nat_from_mask w 8 res in
                                          let (w,res) = get_nat_from_mask w 4 res in
                                              let (w,res) = get_nat_from_mask w 2 res in
                                                  let (w,res) = get_nat_from_mask w 1 res in
                                                        res
"

end 
