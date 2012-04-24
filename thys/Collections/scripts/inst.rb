#!/usr/bin/ruby

# Simple ruby-script to instantiate generic algorithms
#
# Processes preprocessor commands on standard input, and writes preprocessed data to standard output.
#
# A preprocessor command has to start with "(*#" at the very beginning of a line.
#
# For a usage example, see StdInst.in.thy
#
# There are block commands and single-line commands. A block command has the form:
#   (*#command arguments
#      Text (may span multiple lines)
#   *)
#
# A single-line command has the form 
#   (*#command arguments *)
#
# Currently, the following commands are supported:
#   (*#implementations
#       class name abbrv sabbrv
#       ...
#   *)
#   Declares implementations of interfaces. An implementation declaration includes the implemented interface,
#   the implementation name and its two-letter and one-letter abbreviation.
#
#  ----------------------------
#
#   (*#patterns
#      name@intf: p1 ... pn \<Rightarrow> target | <exclusions>
#      name@!: p1 ... pn \<Rightarrow> target | <exclusions>
#   *)
#
#   Where the pi have the form:
#     (x1:t1,...,xn:tn) if-name
#   and target has the form:
#     (x1,...,xn) target-name
#
#   The "| <exclusions>" are optional, and exclusions have the form 
#     var1\<notin>i11,...,i1n ... varm\<notin>im1,...,imn
#   where var refers to variables, and ijk to interface names.
#
#
#   Declares a generic algorithm by a rule how a new function is implemented by existing functions.
#   The name@intf declaration specifies the name of the generic algorithm's constant and the name of the
#   implemented interface. The form name@! declares a generic algorithm with ad-hoc specification.
#
#   The rest of a line is a rule that describes generic algorithm. It may contain variables that are
#   typed by interfaces. The rule p1 ... pn \<Rightarrow> target means, that the generic algorithm has
#   function parameters p1 ... pn, and the instantiated constant shall be named target.
#   The function parameters may depend on variables representing the involved implementations.
#   For example, consider the declaration:
#
#     subset_equal@set_equal: (x:set,y:set)subset (y,x)subset \<Rightarrow> (x,y)equal
#
#   It declares a generic algorithm for checking equality between two sets.
#       The generic algorithm has the constant subset_equal, and implements the interface
#       set_equal. The function parameters are two subset functions, one checking whether an
#       instance of set implementation x is subset of an instance of set implementation y, and the other
#       checking the opposite. Note that the type of a variable needs only be specified once.
#       If the generic algorithm is instantiated, constants named xy_equal will be generated, where
#       x and y are the abbreviations of the implementations substituted for variables x and y.
#       If there is more than one variable involved in target, one-letter abbreviations will be used,
#       otherwise, the implementations two-letter abbreviation is used.
#
#  ----------------------------
#
#   (*#explicit x:t1 ... z:tn
#       text. The following variables are expanded in this text:
#           $s -  expands to the one-letter abbreviations of the implementations currently substituted for the
#                 variables, in order of variable declaration.
#           $x -  expands to the two-letter abbreviation of the implementation currently substituted for x.
#           $!x - expands to the one-letter abbreviation of the implementation currently substituted for x.
#   *)
#
#   Substitute all possible implementations for the declared variables, and, for each substitution, expand the
#   text of the command. Note that variable names must be one letter only, and the variable name "s" is
#   reserved.
#
#  ----------------------------
#   (*# insert_generated *)
#   Insert all instantiations of the declared patterns here. (cf. #pattern-command)
#

class Arg
  attr_accessor :pars, :name, :vdom

  def initialize string
    parse string
  end

  def parse string
    # (x:set,y:map,z)name
    if not (/^\(([A-Za-z,':]+)\)([A-Za-z_']+)$/ =~ string) then 
      raise "Syntax error in pattern: "+string.to_s
    end
  
    @name = $2
    @vdom={}
    @pars=[]

    $1.split(",").each do |p|
      (pn,pd) = p.split(":");
      if pd or not @vdom[pn] then @vdom[pn]=pd end
      @pars << pn
    end
  end

  def instantiate sigma
    return self.get_inst_prefix(sigma) + "_" + @name
  end

  def get_inst_prefix sigma
    if @pars.size==1 then
      return $abbrv[sigma[@pars[0]]]
    else
      return @pars.map{|p| $sabbrv[sigma[p]]}.join
    end
  end

  def get_base_seq sigma
    return @pars.map{|p| a=$abbrv[sigma[p]]; "#{a}_\\<alpha> #{a}_invar"}
  end

  def inspect
    "(" + @pars.join(",") + ")" + @name
  end
end

def merge_vdom vd1,vd2
  res=vd1
  vd2.each do |n,d|
    if not res[n] then 
      res[n]=d;
    elsif d and res[n] != d then
      raise "Variable conflict, "+n+" declared as "+res[n].to_s+" and "+d.to_s
    end
  end

  res
end

class Pattern
  attr_accessor :vdom, :args, :target, :name, :fname, :direct_correctness, :exclude_impls

  def initialize string
    parse string
  end

  def parse string
    # name: a1 ... an \<Rightarrow> rp
    @vdom={}
    @args=[]
    @exclude_impls={}

    if not (/^([A-Za-z_'.]+)@([A-Za-z_']+|!):? *(.*)\\<Rightarrow>([^|]*)(\|(.*))?$/ =~ string) then 
      raise("Syntax error in: "+string) 
    end

    @name,@fname,s_args,s_target,s_excl=[$1,$2,$3,$4,$6]
    @direct_correctness = (@fname == "!")

    # arguments
    s_args.split(/ +/).each do |as|
      a=Arg.new(as.strip)

      @args << a

      @vdom = merge_vdom @vdom,a.vdom
    end

    # target
    @target = Arg.new(s_target.strip)

    # Exclusions (| x\<notin>Impl1,...,Impln)
    if (s_excl != nil) then
      s_excl.strip.split(/ +/).each do |as|
        if not (/^([A-Za-z_'])\\<notin>([A-Za-z_',]+)$/ =~ as) then
          raise("Syntax error in exclude pattern: "+as)
        end
        s_name,s_ilist=[$1,$2]
        @exclude_impls[s_name]={} unless @exclude_impls.has_key? s_name

        s_ilist.split(/,/).each do |iname|
          @exclude_impls[s_name][iname]=true
        end
      end
    end


  end

  def inspect
    @vdom.inspect + " " + @args.map{|x| x.inspect}.join(" ") + " => " + @target.inspect
  end

  def inst_rec karr,sigma
    if karr.empty? then
      iseq = @args.map{|a| a.instantiate sigma}
      clseq = iseq.map{|x| x+"_impl"}
      cname = @target.instantiate(sigma)
      prefix = @target.get_inst_prefix(sigma)
      baseseq = @target.get_base_seq(sigma)

      puts <<HERE
  definition "#{cname} == #{@name} #{iseq.join(" ")}"
HERE
      if @direct_correctness then
        puts <<HERE
  lemmas #{cname}_correct = #{@name}_correct[OF #{clseq.join(" ")}, folded #{cname}_def]
HERE
      else
        puts <<HERE
  lemmas #{cname}_impl = #{@name}_correct[OF #{clseq.join(" ")}, folded #{cname}_def]
  interpretation #{prefix}: #{@fname} #{baseseq.join(" ")} #{cname} using #{cname}_impl .
HERE
      end

#       @args.each do |a|
#         puts a.instantiate(sigma)
#       end
#       puts " => "
#       puts target.instantiate(sigma)
#       puts "-------------"
    else
      karrn=karr.clone
      var=karrn.shift

      $impl[@vdom[var]].each do |i|
        if not @exclude_impls[var] or not @exclude_impls[var][i] then
          sigma[var]=i
          inst_rec karrn,sigma
        end
      end
    end
  end

  def instantiate
    self.inst_rec @vdom.keys,{}
  end

end

def inst_rec (karr, idx, vdom, sigma, it)
  if idx == karr.size then
    it.call(sigma)
  else
    var = karr[idx]
    $impl[vdom[var]].each do |val|
      sigma[var]=val
      inst_rec(karr,idx+1,vdom,sigma,it)
    end
  end
end

def instantiate (vdom, &it)
  inst_rec(vdom.keys,0,vdom,{},it)
end

def parse_impl string
  a = string.strip.split(/ +/)
  if a.size != 4 then raise "Syntax error on impl: "+string end
  (cls,name,abbrv,sabbrv) = a

  $impl[cls]=[] unless $impl.has_key? cls
  $impl[cls] << name
  $abbrv[name] = abbrv
  $sabbrv[name] = sabbrv
end

$impl={}
$abbrv={}
$sabbrv={}
$patterns=[]

puts "(* Generated file *)"

while gets
  case
    when ~/^\(\*#implementations *$/ then
      while gets and ($_.strip != "*)")
        parse_impl $_.strip
      end

    when ~/^\(\*#patterns *$/ then
      while gets and ($_.strip != "*)")
        string = $_.strip
        if string != "" then
          $patterns << Pattern.new(string)
        end
      end

    when ~/^\(\*#explicit *(.*)$/ then
      text=""
      args=$1.strip.split(/ +/)
      while gets and ($_.strip != "*)")
        text=text+$_
      end

      vdom={}
      vlist=[]
      args.each do |a|
        vn,vd = a.split(":")
        vdom[vn]=vd
        vlist << vn
      end

      puts "(*#begin_generated*)"
      instantiate vdom do |sigma|
        puts(text.gsub(/\$!?./) {|match| 
          case
            when match[1,1]=="s" then
              vlist.map{|x| $sabbrv[sigma[x]]}.join
            when (match[1,1]=="!") && (vdom.has_key?(match[2,2])) then
              $sabbrv[sigma[match[2,2]]]
            when vdom.has_key?(match[1,1]) then
              $abbrv[sigma[match[1,1]]]
            else match
          end
        })
      end
      puts "(*#end_generated*)"

    when ~/^\(\*#insert_generated *\*\) *$/ then
      puts "(*#begin_generated*)"
      $patterns.each do |p|
        puts ""
        p.instantiate
      end
      puts "(*#end_generated*)"
    else
      puts $_

  end
end
