#!/usr/bin/perl
#
# Author: Gerwin Klein, NICTA
#
# Parses log file and generates report of entry status.
# Prints out diff to last report.
#
# ASSUMPTION: names in ROOTS = all session names
#
# Alternative?
# isabelle build -d ../thys -g AFP -c -n -v | grep ^Session | cut -c 9- | grep "(AFP)" | rev | cut -c 7- | rev


if ($#ARGV!=2) {
  print "usage: $0 <rootsfile> <logfile> <report-file>\n";
  exit 1;
}

$roots=$ARGV[0];
$logfile=$ARGV[1];
$report=$ARGV[2];

$FAIL="FAIL";
$FAIL_N="FAIL (new)";
$OK="ok";

#read ROOTS file
open (IN,$roots) || die "could not open [$roots]";
@sessions = <IN>;
close IN;

# read log file
open (IN,$logfile) || die "could not open [$logfile]";
@lines = <IN>;
close IN;

# parse log file
for $i (0 .. $#lines) {
  $_ = $lines[$i];
  if ( /^Finished ([^ ]+)/ ) {
    $finished{$1} = 1;
  }  
  if ( /Unfinished session\(s\)/ ) {
    foreach $f (split (/[, \n]/,$lines[$i])) {
      $unfinished{$f} = 1;
    }
  }
}

# read and parse old report
open (IN,$report);
while (<IN>) {
  chop;
  ($name, $f) = split /[:]/;
  $old_sessions{$name} = 1;
  $old_status{$name} = $f;
  $old_ok{$name} = ($f =~ /$OK/);
}
close IN;

# save old report
rename ($report, $report.".old");

# write new report
open (OUT,">$report") || die "could not open [$report] for writing.";
foreach $s (@sessions) {
  chomp($s);
  if ($finished{$s}) {
    $new_status{$s} = $OK;
  } elsif (!$old_sessions{$s} or $old_status{$s} eq " $FAIL_N") {
    $new_status{$s} = $FAIL_N;
  } else {
    $new_status{$s} = $FAIL;
  }
  print OUT "$s: $new_status{$s}\n";
}
close OUT;

# output diff
foreach $t (keys %old_sessions) {
  if (!($t ~~ @sessions)) {
    print "[$t] was removed. Last status was $old_status{$t}.\n";
  }
  elsif ($old_ok{$t} != $finished{$t}) {
    print "[$t] changed from $old_status{$t} to $new_status{$t}.\n";
  }
  elsif (!$finished{$t}) {
    print "[$t] is still on $new_status{$t}.\n";
  }
}

foreach $t (@sessions) {
  if (!$old_sessions{$t}) {
    print "[$t] is new. Status is $new_status{$t}.\n";
  }
}
