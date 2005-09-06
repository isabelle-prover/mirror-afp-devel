(*  Title:      Jinja/Common/Value.thy
    ID:         $Id: Value.thy,v 1.2 2005-09-06 15:06:08 makarius Exp $
    Author:     David von Oheimb, Tobias Nipkow
    Copyright   1999 Technische Universitaet Muenchen
*)

header {* \isaheader{Jinja Values} *}

theory Value imports TypeRel begin

types addr = nat

datatype val
  = Unit        -- "dummy result value of void expressions"
  | Null        -- "null reference"
  | Bool bool   -- "Boolean value"
  | Intg int    -- "integer value" 
  | Addr addr   -- "addresses of objects in the heap"

consts
  the_Intg :: "val \<Rightarrow> int"
  the_Addr :: "val \<Rightarrow> addr"

primrec
  "the_Intg (Intg i) = i"

primrec
  "the_Addr (Addr a) = a"

consts
  default_val :: "ty \<Rightarrow> val"   -- "default value for all types"

primrec
  "default_val Void      = Unit"
  "default_val Boolean   = Bool False"
  "default_val Integer   = Intg 0"
  "default_val NT        = Null"
  "default_val (Class C) = Null"

end
