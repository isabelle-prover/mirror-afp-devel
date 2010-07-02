(*  Title:       Isabelle Collections Library
    Author:      Peter Lammich <peter dot lammich at uni-muenster.de>
    Maintainer:  Peter Lammich <peter dot lammich at uni-muenster.de>
*)
header "The Hashable Typeclass"
theory HashCode
imports Main
begin
text_raw {*\label{thy:HashCode}*}


text {*
  In this theory a typeclass of hashable types is established.
  For hashable types, there is a function @{text hashcode}, that
  maps any entity of this type to an integer value.

  This theory defines the hashable typeclass and provides instantiations 
  for a couple of standard types.
*}

types 
  hashcode = "int"

class hashable =
  fixes hashcode :: "'a \<Rightarrow> hashcode"
  (* assumes "a=b \<Longrightarrow> hashcode a = hashcode b" *)

instantiation unit :: hashable 
begin
  definition "hashcode_of_unit (u::unit) = (0::int)"
  definition [simp]: "hashcode = hashcode_of_unit"
  instance ..
end

instantiation "int" :: hashable
begin
  definition hashcode_int_def[simp]: "hashcode i == i"
  instance ..
end

instantiation "nat" :: hashable
begin
  definition hashcode_nat_def[simp]: "hashcode i == int i"
  instance ..
end


instantiation prod :: (hashable, hashable) hashable
begin
  definition hashcode_prod_def: 
    "hashcode x == case x of (a,b) \<Rightarrow> hashcode a + hashcode b"
  instance ..
end

instantiation "nibble" :: hashable
begin
  fun num_of_nibble :: "nibble \<Rightarrow> int"
    where
    "num_of_nibble Nibble0 = 0" |
    "num_of_nibble Nibble1 = 1" |
    "num_of_nibble Nibble2 = 2" |
    "num_of_nibble Nibble3 = 3" |
    "num_of_nibble Nibble4 = 4" |
    "num_of_nibble Nibble5 = 5" |
    "num_of_nibble Nibble6 = 6" |
    "num_of_nibble Nibble7 = 7" |
    "num_of_nibble Nibble8 = 8" |
    "num_of_nibble Nibble9 = 9" |
    "num_of_nibble NibbleA = 10" |
    "num_of_nibble NibbleB = 11" |
    "num_of_nibble NibbleC = 12" |
    "num_of_nibble NibbleD = 13" |
    "num_of_nibble NibbleE = 14" |
    "num_of_nibble NibbleF = 15"

  definition [simp]: "hashcode == num_of_nibble"
  instance ..
end

instantiation char :: hashable 
begin
  fun hashcode_of_char :: "char \<Rightarrow> int" where
    "hashcode_of_char (Char a b) = hashcode a + hashcode b"

  definition [simp]: "hashcode == hashcode_of_char"
  instance ..
end

instantiation list :: (hashable) hashable
begin
  fun hashcode_of_list :: "'a list \<Rightarrow> hashcode" where
    "hashcode_of_list [] = 0" |
    "hashcode_of_list (x#xs) = hashcode x + hashcode_of_list xs"

  definition [simp]: "hashcode = hashcode_of_list"

  instance ..
end

instantiation option :: (hashable) hashable
begin
  fun hashcode_of_option :: "'a option \<Rightarrow> hashcode" where
    "hashcode_of_option None = 0" |
    "hashcode_of_option (Some x) = hashcode x"

  definition [simp]: "hashcode = hashcode_of_option"

  instance ..
end


end
