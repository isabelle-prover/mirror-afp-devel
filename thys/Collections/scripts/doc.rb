#!/usr/bin/ruby

class DocItem
  attr_accessor :type, :text, :tags, :theory
  
  def initialize type,text,tags,theory
    @type=type
    @text=text
    @tags=tags
    @theory=theory
  end

  def pos
    return "in theory #{@theory}"
  end
  
  def warn msg
    $stderr.puts "Warning (#{self.pos}): #{msg}"
  end
  
end

# Parse
$dis = []
theory = "<unknown>"

while gets
  
  if ~/^\s*theory\s*(\w+)/ then 
    theory = $1.strip
  end
  
  case
  when ~/^\s*\(\*\s*@(\w+)(.*)$/ then  
    type=$1
    str=$2.strip
    
    text = ""
    tags = {type => str}
    
    while gets
      case 
      when ~/\*\)/ then break
      when ~/^\s*@(\w+)(.*)$/
        tags[$1] = $2.strip;
      else text = text + $_
      end
    end

    $dis << (DocItem.new type,text.strip,tags,theory)
  end
end

# Build indices

$interfaces = {}
$implementations = []

def isatext s
  return "@{text \"#{s.gsub /"/,'\\isachardoublequote'}\"}"
end


def allowed_tags di,tl
  di.tags.each_key { |t| di.warn "Undefined tag: @#{t}" unless tl.include? t }
end

def expected_tags di,tl
  tl.each { |t| di.warn "Expected tag: @#{t}" unless di.tags.has_key? t }
end

class Interface
  attr_accessor :di, :name, :impls

  def initialize di
    throw 'Expected intf-type' unless di.type == 'intf';

    allowed_tags di,['intf','abstype']
    expected_tags di,['abstype']
    
    @di=di
    @name = di.tags['intf']
    @impls = []
    
    di.warn "Duplicate interface: #{@name}" if $interfaces.has_key? @name;
    $interfaces[name] = self
  end

  
  def output_latex
    puts "\\docIntf{#{isatext name}}{#{isatext @di.theory}}"
    puts "\\docAbstype{#{isatext @di.tags['abstype']}}" if @di.tags['abstype'];
    puts "\\docDesc{#{@di.text}}"
    
    puts "\\begin{docImpls}"
    @impls.each {|i| i.output_latex}
    puts "\\end{docImpls}"
  end
  
end

class Implementation
  attr_accessor :di, :type, :intf

  def initialize di
    throw 'Expected impl-type' unless di.type == 'impl';

    allowed_tags di,['impl','type','abbrv']
    expected_tags di,['type']
        
    @di=di
    @type = di.tags['type']
    @intf=nil
    
    $implementations << self
  end
  
  def resolve
    intf_name = @di.tags['impl'];
    @intf = $interfaces[intf_name]
    
    if @intf == nil then
      di.warn "Undefined interface: #{intf_name}"
    else
      @intf.impls << self if @intf != nil;
    end
    
  end
  
  
  def output_latex
    puts "\\docImpl{#{isatext @di.theory}}"
    puts "\\docType{#{isatext @di.tags['type']}}" if @di.tags['type'];
    puts "\\docAbbrv{#{isatext @di.tags['abbrv']}}" if @di.tags['abbrv'];
    puts "\\docDesc{#{@di.text}}"
  end
  

end

  
$dis.each { |di|
    case di.type 
      when 'intf' then Interface.new di;
      when 'impl' then Implementation.new di;
      else puts "Unknown documentation type: #{di.type}";
    end
}

$implementations.each { |i| i.resolve }

$unres_impl = []
$implementations.each { |i| if i.intf==nil then $unres_impl << i end }


# Output

puts <<EOF
header {* \\isaheader{Overview of Interfaces and Implementations} *}
theory Impl_Overview
imports Main
begin
  text {*
EOF
$interfaces.each_value { |i| i.output_latex }

puts <<EOF
  *}
end
EOF

# $unres_impl.each { |i| i.output_latex }



