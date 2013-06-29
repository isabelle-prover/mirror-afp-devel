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
  $old_ok{$name} = ($f =~ /$OK/);
}
close IN;

# save old report
rename ($report, $report.".old");

# write new report
open (OUT,">$report") || die "could not open [$report] for writing.";
foreach $s (@sessions) {
  chomp($s);
  $status = $finished{$s} ? $OK : $FAIL;
  print OUT "$s: $status\n";
}
close OUT;

# output diff
foreach $t (keys %old_sessions) {
  $old_status = $old_ok{$t} ? $OK : $FAIL;
  $new_status = $finished{$t} ? $OK : $FAIL;
  if (!$t ~~ @sessions) {
    print "[$t] was removed. Last status was $old_status.\n";
  }
  elsif ($old_ok{$t} != $finished{$t}) {
    print "[$t] changed from $old_status to $new_status.\n";
  }
  elsif (!$finished{$t}) {
    print "[$t] is still on $new_status.\n";
  }
}

foreach $t (@sessions) {
  if (!$old_sessions{$t}) {
    $new_status = $finished{$t} ? $OK : $FAIL;
    print "[$t] is new. Status is $new_status.\n";
  }
}
